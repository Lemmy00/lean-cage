// SPDX-License-Identifier: Apache-2.0
// §AR-host-boundary.interfaces: Marshal bounded native values into one fixed host invocation.
#define _GNU_SOURCE
#define Py_LIMITED_API 0x030b0000
#include <Python.h>
#include <dlfcn.h>
#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <signal.h>
#include <spawn.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

#define HOST_FIELDS 8
#define HOST_PATH_MAX 4095
#define HOST_POLICY_MAX 65536
#define HOST_STDIN_MAX 67108864
#define HOST_RESPONSE_MAX 536870912
#define HOST_VALUE_NODES 1048576
#define HOST_VALUE_DEPTH 72
#define HOST_STRING_MAX 16777216
#define HOST_BYTES_MAX 268435456

struct host_field {
    uint32_t kind;
    uint64_t size;
    const char *data;
    PyObject *root;
    unsigned char scalar[8];
};

typedef struct {
    PyObject_HEAD
    PyObject *bundle;
    PyObject *results;
    PyObject *information;
} HostWorkspace;

typedef struct {
    PyObject_HEAD
    int cancelled;
} HostCancellation;

typedef struct {
    PyObject_HEAD
    PyObject *data;
} HostOutcome;

#include "host_python_primitives.h"

static char host_root[HOST_PATH_MAX + 1];
static char host_engine[HOST_PATH_MAX + 1];
static char host_default_results[HOST_PATH_MAX + 1];
static PyObject *host_path_class;
static PyObject *host_cancellation_class;
static PyObject *host_outcome_class;
static volatile sig_atomic_t host_cli_cancelled;
static int host_cli_active;
static int host_initialized;
static const char host_unavailable_error[32];

PyMODINIT_FUNC PyInit__host(void);
static int host_parse_objects(PyObject *args, PyObject *keywords, const char *format,
                              char *const *names, unsigned count, unsigned required,
                              int keyword_only, PyObject ***outputs);
static PyObject *host_call_objects(PyObject *callable, PyObject *const *values, unsigned count);
static PyObject *host_outcome_observation(HostOutcome *self, void *unused);
static const char host_observation_name[12];

static void host_put32(unsigned char *p, uint32_t value) {
    for (unsigned index = 0; index < 4; index++) p[index] = (unsigned char)(value >> (8 * index));
}
static void host_put64(unsigned char *p, uint64_t value) {
    for (unsigned index = 0; index < 8; index++) p[index] = (unsigned char)(value >> (8 * index));
}
static uint64_t host_get64(const unsigned char *p, unsigned width) {
    uint64_t value = 0;
    for (unsigned index = 0; index < width; index++) value |= (uint64_t)p[index] << (8 * index);
    return value;
}

// §FS-host-boundary.caller: Guard signed runtime lengths before any narrowing or native use.
int host_gateway_size(long size, unsigned long maximum) {
    if (size < 0) return -1;
    if ((unsigned long)size > maximum) return -1;
    return 0;
}

static void host_field_clear(struct host_field *field) {
    PyObject *old = field->root;
    field->root = NULL;
    if (old) Py_DecRef(old);
}

// §FS-host-boundary.caller: Immutable bytes have an independent strong root across all I/O.
static int host_field_bytes(struct host_field *field, PyObject *object, uint32_t kind, long maximum) {
    char *data;
    Py_ssize_t size;
    if (PyBytes_AsStringAndSize(object, &data, &size)) return -1;
    if (host_gateway_size((long)size, (unsigned long)maximum)) {
        PyErr_SetString(PyExc_ValueError, "host argument exceeds its byte bound");
        return -1;
    }
    Py_IncRef(object);
    field->kind = kind;
    field->size = (uint64_t)size;
    field->data = data;
    field->root = object;
    return 0;
}

// §FS-host-boundary.caller: PathLike values use the interpreter's filesystem codec, not UTF-8.
static int host_field_path(struct host_field *field, PyObject *object) {
    PyObject *path = PyOS_FSPath(object);
    if (!path) return -1;
    int is_bytes = PyObject_IsInstance(path, (PyObject *)&PyBytes_Type);
    if (is_bytes < 0) { Py_DecRef(path); return -1; }
    PyObject *bytes;
    if (is_bytes) { bytes = path; Py_IncRef(bytes); }
    else {
        Py_ssize_t characters = PyUnicode_GetLength(path);
        if (characters < 0) { Py_DecRef(path); return -1; }
        if (characters > HOST_PATH_MAX) {
            Py_DecRef(path); PyErr_SetString(PyExc_ValueError, "filesystem path exceeds its bound");
            return -1;
        }
        bytes = PyUnicode_EncodeFSDefault(path);
    }
    Py_DecRef(path);
    if (!bytes) return -1;
    int result = host_field_bytes(field, bytes, 2, HOST_PATH_MAX);
    Py_DecRef(bytes);
    if (!result && memchr(field->data, 0, (size_t)field->size)) {
        host_field_clear(field);
        PyErr_SetString(PyExc_ValueError, "embedded NUL in filesystem path");
        return -1;
    }
    return result;
}

static int host_field_input(struct host_field *field, PyObject *object, long maximum) {
    int is_bytes = PyObject_IsInstance(object, (PyObject *)&PyBytes_Type);
    if (is_bytes < 0) return -1;
    if (is_bytes) return host_field_bytes(field, object, 1, maximum);
    return host_field_path(field, object);
}

// §FS-host-boundary.caller: Capture relative configuration against the actual constructor cwd.
static int host_field_absolute(struct host_field *field) {
    if (field->size && field->data[0] == '/') return 0;
    char directory[HOST_PATH_MAX + 1], absolute[HOST_PATH_MAX + 1];
    if (!getcwd(directory, sizeof(directory))) { PyErr_SetFromErrno(PyExc_OSError); return -1; }
    size_t prefix = strnlen(directory, sizeof(directory));
    if (prefix > HOST_PATH_MAX || field->size > HOST_PATH_MAX - prefix - (prefix < HOST_PATH_MAX ? 1 : 0) ||
        prefix == HOST_PATH_MAX) {
        PyErr_SetString(PyExc_ValueError, "absolute filesystem path exceeds its bound"); return -1;
    }
    memcpy(absolute, directory, prefix); absolute[prefix] = '/';
    memcpy(absolute + prefix + 1, field->data, (size_t)field->size);
    PyObject *bytes = PyBytes_FromStringAndSize(absolute, (Py_ssize_t)(prefix + 1 + field->size));
    if (!bytes) return -1;
    host_field_clear(field);
    int result = host_field_bytes(field, bytes, 2, HOST_PATH_MAX);
    Py_DecRef(bytes);
    return result;
}

// §AR-host-boundary.interfaces: Only the immutable loaded artifact selects the engine pathname.
static int host_bootstrap(void) {
    static const char suffix[] = "/python/leancage/_host.abi3.so";
    static const char executable[] = "/bin/leancage-host";
    static const char results[] = "/.tools/product/runs";
    Dl_info information;
    if (!dladdr((void *)PyInit__host, &information) || !information.dli_fname) return -1;
    size_t size = strnlen(information.dli_fname, HOST_PATH_MAX + 1);
    size_t tail = sizeof(suffix) - 1;
    if (size > HOST_PATH_MAX || size <= tail || information.dli_fname[0] != '/' ||
        memcmp(information.dli_fname + size - tail, suffix, tail)) return -1;
    size_t api_size = size - tail;
    char resolved[HOST_PATH_MAX + 1];
    if (!realpath(information.dli_fname, resolved)) return -1;
    size = strnlen(resolved, sizeof(resolved));
    if (size > HOST_PATH_MAX || size <= tail || resolved[0] != '/' ||
        memcmp(resolved + size - tail, suffix, tail)) return -1;
    size_t root_size = size - tail;
    if (root_size + sizeof(executable) > sizeof(host_engine)) return -1;
    if (api_size + sizeof(results) > sizeof(host_default_results)) return -1;
    memcpy(host_root, resolved, root_size);
    host_root[root_size] = 0;
    memcpy(host_engine, host_root, root_size);
    memcpy(host_engine + root_size, executable, sizeof(executable));
    memcpy(host_default_results, information.dli_fname, api_size);
    memcpy(host_default_results + api_size, results, sizeof(results));
    return 0;
}

static double host_now(void) {
    struct timespec sample;
    if (clock_gettime(CLOCK_MONOTONIC, &sample) || sample.tv_sec < 0) return 0;
    return (double)sample.tv_sec + (double)sample.tv_nsec / 1000000000.0;
}

struct host_stream {
    int descriptor;
    int control;
    int cancellation_sent;
    int cli;
    HostCancellation *cancellation;
    uint64_t remaining;
    uint64_t nodes;
    double deadline;
};

// §FS-host-boundary.caller: Cancellation is a request to the owned engine, not cleanup evidence.
static int host_control(struct host_stream *stream) {
    if (stream->cancellation_sent ||
        (!(stream->cancellation && stream->cancellation->cancelled) &&
         !(stream->cli && host_cli_cancelled))) return 0;
    unsigned char command = 'C';
    ssize_t count = send(stream->control, &command, 1, MSG_NOSIGNAL);
    if (count == 1) { stream->cancellation_sent = 1; return 0; }
    if (count < 0 && (errno == EINTR || errno == EAGAIN || errno == EWOULDBLOCK)) return 0;
    // The engine may already have flushed its result and closed FD3. Keep that observation.
    stream->cancellation_sent = 1;
    return 0;
}

static int host_ready(struct host_stream *stream, short events) {
    for (;;) {
        if (host_control(stream)) return -1;
        double now = host_now();
        if (!now || now >= stream->deadline) {
            PyErr_SetString(PyExc_TimeoutError, "host engine deadline expired");
            return -1;
        }
        struct pollfd item = { stream->descriptor, events, 0 };
        PyThreadState *saved = PyEval_SaveThread();
        int result = poll(&item, 1, 100);
        int number = errno;
        PyEval_RestoreThread(saved);
        if (PyErr_CheckSignals()) return -1;
        if (result < 0 && number != EINTR) {
            errno = number;
            PyErr_SetFromErrno(PyExc_OSError);
            return -1;
        }
        if (result > 0) return 0;
    }
}

// §FS-host-boundary.transport: Each returned count is checked before advancing the live buffer.
static int host_transfer(struct host_stream *stream, void *data, uint64_t size, int sending) {
    unsigned char *cursor = data;
    while (size) {
        if (host_ready(stream, sending ? POLLOUT : POLLIN)) return -1;
        size_t amount = size > 65536 ? 65536 : (size_t)size;
        PyThreadState *saved = PyEval_SaveThread();
        ssize_t count = sending ? send(stream->descriptor, cursor, amount, MSG_NOSIGNAL) :
                                  recv(stream->descriptor, cursor, amount, 0);
        int number = errno;
        PyEval_RestoreThread(saved);
        if (count < 0 && (number == EINTR || number == EAGAIN || number == EWOULDBLOCK)) continue;
        if (count <= 0 || (size_t)count > amount) {
            PyErr_SetString(PyExc_ValueError, "host engine channel lost or invalid count");
            return -1;
        }
        cursor += count;
        size -= (uint64_t)count;
    }
    return 0;
}

static int host_read(struct host_stream *stream, void *data, uint64_t size) {
    if (size > stream->remaining) {
        PyErr_SetString(PyExc_ValueError, "truncated host value");
        return -1;
    }
    if (host_transfer(stream, data, size, 0)) return -1;
    stream->remaining -= size;
    return 0;
}

static int host_word(struct host_stream *stream, unsigned width, uint64_t *value) {
    unsigned char bytes[8];
    if (width > sizeof(bytes) || host_read(stream, bytes, width)) return -1;
    *value = host_get64(bytes, width);
    return 0;
}

// §FS-host-boundary.caller: Parse one JSON number, never an opaque report or JSON document.
static PyObject *host_json_number(const char *bytes, size_t size) {
    size_t index = 0;
    int negative = size && bytes[0] == '-';
    if (negative) index++;
    size_t digits = index;
    if (index == size) goto invalid;
    if (bytes[index] == '0') index++;
    else {
        if (bytes[index] < '1' || bytes[index] > '9') goto invalid;
        do { index++; } while (index < size && bytes[index] >= '0' && bytes[index] <= '9');
    }
    size_t integer_end = index;
    if (index < size && bytes[index] == '.') {
        size_t fraction = ++index;
        while (index < size && bytes[index] >= '0' && bytes[index] <= '9') index++;
        if (index == fraction) goto invalid;
    }
    if (index < size && (bytes[index] == 'e' || bytes[index] == 'E')) {
        index++;
        if (index < size && (bytes[index] == '+' || bytes[index] == '-')) index++;
        size_t exponent = index;
        while (index < size && bytes[index] >= '0' && bytes[index] <= '9') index++;
        if (index == exponent) goto invalid;
    }
    if (index != size) goto invalid;
    if (integer_end != size) {
        PyObject *text = PyUnicode_DecodeUTF8(bytes, (Py_ssize_t)size, "strict");
        if (!text) return NULL;
        PyObject *value = PyFloat_FromString(text);
        Py_DecRef(text);
        return value;
    }
    PyObject *value = PyLong_FromLong(0), *base = PyLong_FromUnsignedLong(1000000000UL);
    if (!value || !base) {
        if (value) Py_DecRef(value);
        if (base) Py_DecRef(base);
        return NULL;
    }
    index = digits;
    size_t width = (size - digits) % 9;
    if (!width) width = 9;
    while (index < size) {
        unsigned long chunk = 0;
        for (size_t offset = 0; offset < width; offset++)
            chunk = 10 * chunk + (unsigned long)(bytes[index + offset] - '0');
        PyObject *part = PyLong_FromUnsignedLong(chunk);
        if (!part) { Py_DecRef(base); Py_DecRef(value); return NULL; }
        PyObject *scaled = PyNumber_Multiply(value, base);
        Py_DecRef(value);
        if (!scaled) { Py_DecRef(base); Py_DecRef(part); return NULL; }
        value = PyNumber_Add(scaled, part);
        Py_DecRef(scaled); Py_DecRef(part);
        if (!value) { Py_DecRef(base); return NULL; }
        index += width; width = 9;
    }
    Py_DecRef(base);
    if (negative) {
        PyObject *signed_value = PyNumber_Negative(value);
        Py_DecRef(value); value = signed_value;
    }
    return value;
invalid:
    PyErr_SetString(PyExc_ValueError, "invalid host JSON number");
    return NULL;
}

static PyObject *host_value(struct host_stream *stream, unsigned depth) {
    uint64_t tag, size;
    if (!depth || !stream->nodes) {
        PyErr_SetString(PyExc_ValueError, "host response depth or node bound exceeded");
        return NULL;
    }
    stream->nodes--;
    if (host_word(stream, 1, &tag)) return NULL;
    if (!tag) { Py_IncRef(Py_None); return Py_None; }
    if (tag == 1 || tag == 2) return PyBool_FromLong(tag == 2);
    if ((tag >= 3 && tag <= 6) || tag == 9) {
        if (host_word(stream, tag == 3 ? 4 : 8, &size)) return NULL;
        uint64_t maximum = tag == 3 ? 32 : tag == 4 ? HOST_STRING_MAX :
                           tag == 5 ? HOST_BYTES_MAX : tag == 9 ? HOST_POLICY_MAX : HOST_PATH_MAX;
        if (size > maximum || size > stream->remaining) {
            PyErr_SetString(PyExc_ValueError, "host value payload exceeds its bound");
            return NULL;
        }
        char *bytes = malloc((size_t)size + 1);
        if (!bytes) return PyErr_NoMemory();
        if (host_read(stream, bytes, size)) { free(bytes); return NULL; }
        bytes[size] = 0;
        PyObject *value = NULL;
        if (tag == 3) {
            size_t start = size && bytes[0] == '-' ? 1 : 0;
            int valid = start < size && (size - start == 1 || bytes[start] != '0') &&
                        !(start && size == 2 && bytes[1] == '0');
            for (size_t index = start; index < size; index++)
                if (bytes[index] < '0' || bytes[index] > '9') valid = 0;
            if (valid) value = PyLong_FromString(bytes, NULL, 10);
            else PyErr_SetString(PyExc_ValueError, "noncanonical host integer");
        } else if (tag == 9) value = host_json_number(bytes, (size_t)size);
        else if (tag == 4) value = PyUnicode_DecodeUTF8(bytes, (Py_ssize_t)size, "strict");
        else if (tag == 5) value = PyBytes_FromStringAndSize(bytes, (Py_ssize_t)size);
        else if (memchr(bytes, 0, (size_t)size))
            PyErr_SetString(PyExc_ValueError, "NUL in returned filesystem path");
        else value = PyUnicode_DecodeFSDefaultAndSize(bytes, (Py_ssize_t)size);
        free(bytes);
        return value;
    }
    if (tag == 7 || tag == 8) {
        if (host_word(stream, 4, &size)) return NULL;
        if (size > (tag == 8 ? stream->nodes / 2 : stream->nodes)) {
            PyErr_SetString(PyExc_ValueError, "host container exceeds node bound");
            return NULL;
        }
        PyObject *container = tag == 7 ? PyList_New(0) : PyDict_New();
        if (!container) return NULL;
        for (uint64_t index = 0; index < size; index++) {
            PyObject *first = host_value(stream, depth - 1);
            if (!first) { Py_DecRef(container); return NULL; }
            if (tag == 7) {
                int result = PyList_Append(container, first);
                Py_DecRef(first);
                if (result) { Py_DecRef(container); return NULL; }
            } else {
                int string_key = PyObject_IsInstance(first, (PyObject *)&PyUnicode_Type);
                int duplicate = string_key > 0 ? PyDict_Contains(container, first) : -1;
                if (string_key <= 0 || duplicate) {
                    Py_DecRef(first); Py_DecRef(container);
                    if (!PyErr_Occurred()) PyErr_SetString(PyExc_ValueError, "invalid host object key");
                    return NULL;
                }
                PyObject *value = host_value(stream, depth - 1);
                if (!value) { Py_DecRef(first); Py_DecRef(container); return NULL; }
                int result = PyDict_SetItem(container, first, value);
                Py_DecRef(first); Py_DecRef(value);
                if (result) { Py_DecRef(container); return NULL; }
            }
        }
        return container;
    }
    PyErr_SetString(PyExc_ValueError, "unknown host value tag");
    return NULL;
}

// §FS-host-boundary.caller: Preserve typed filesystem errno and filename observations.
static void host_raise(uint64_t status, PyObject *value) {
    if (status != 2) {
        PyErr_SetObject(status == 1 ? PyExc_ValueError : PyExc_TimeoutError, value);
        return;
    }
    int object = PyObject_IsInstance(value, (PyObject *)&PyDict_Type);
    if (object < 0) return;
    if (!object) { PyErr_SetObject(PyExc_OSError, value); return; }
    PyObject *number = PyDict_GetItemString(value, "errno");
    PyObject *message = PyDict_GetItemString(value, "message");
    PyObject *filename = PyDict_GetItemString(value, "filename");
    if (!number || !message) {
        PyErr_SetString(PyExc_ValueError, "incomplete host filesystem error");
        return;
    }
    int number_type = PyObject_IsInstance(number, (PyObject *)&PyLong_Type);
    if (number_type < 0) return;
    int message_type = PyObject_IsInstance(message, (PyObject *)&PyUnicode_Type);
    if (message_type < 0) return;
    if (!number_type || !message_type) {
        PyErr_SetString(PyExc_ValueError, "invalid host filesystem error fields");
        return;
    }
    PyObject *path = filename && filename != Py_None ? PyOS_FSPath(filename) : NULL;
    if (filename && filename != Py_None && !path) return;
    PyObject *arguments[] = { number, message, path };
    PyObject *error = host_call_objects(PyExc_OSError, arguments, path ? 3 : 2);
    if (path) Py_DecRef(path);
    if (!error) return;
    PyErr_SetObject(PyExc_OSError, error);
    Py_DecRef(error);
}

// §FS-host-boundary.caller: Fresh private descriptors are disjoint from fixed child ABI slots.
static int host_private_pair(int pair[2]) {
    if (socketpair(AF_UNIX, SOCK_STREAM | SOCK_CLOEXEC | SOCK_NONBLOCK, 0, pair)) return -1;
    for (unsigned index = 0; index < 2; index++) {
        if (pair[index] < 4) {
            int moved = leancage_host_fcntl(pair[index], F_DUPFD_CLOEXEC, 4);
            if (moved < 0) {
                int number = errno; close(pair[0]); close(pair[1]); errno = number; return -1;
            }
            close(pair[index]); pair[index] = moved;
        }
    }
    return 0;
}

// §FS-host-boundary.ownership: Raw signal targets require the lifetime proof tracked for M5.4.
static void host_engine_reap(pid_t child, int complete) {
    if (!complete) kill(-child, SIGKILL);
    double began = host_now();
    int status;
    for (;;) {
        pid_t observed = waitpid(child, &status, WNOHANG);
        if (observed == child || (observed < 0 && errno != EINTR)) return;
        double now = host_now();
        if (!began || !now || now >= began + 10.0) break;
        struct timespec pause = { 0, 100000000 };
        nanosleep(&pause, NULL);
    }
    kill(-child, SIGKILL);
    while (waitpid(child, &status, 0) < 0 && errno == EINTR) {}
}

static PyObject *host_exchange(struct host_field fields[HOST_FIELDS], uint32_t command,
                               uint32_t fault, HostCancellation *cancellation, int cli) {
    // §FS-host-boundary.caller.initialization: Exposed classes require completed setup.
    if (!host_initialized) {
        PyErr_SetString(PyExc_RuntimeError, host_unavailable_error); return NULL;
    }
    double began = host_now();
    if (!began) {
        PyErr_SetString(PyExc_OSError, "host monotonic clock unavailable"); return NULL;
    }
    int pair[2], control[2];
    if (host_private_pair(pair)) return PyErr_SetFromErrno(PyExc_OSError);
    if (host_private_pair(control)) {
        int number = errno; close(pair[0]); close(pair[1]); errno = number;
        return PyErr_SetFromErrno(PyExc_OSError);
    }
    int flags = leancage_host_fcntl(pair[1], F_GETFL, 0);
    if (flags < 0 || leancage_host_fcntl(pair[1], F_SETFL, flags & ~O_NONBLOCK)) {
        int number = errno; close(pair[0]); close(pair[1]); close(control[0]); close(control[1]);
        errno = number; return PyErr_SetFromErrno(PyExc_OSError);
    }
    posix_spawn_file_actions_t actions;
    int setup = posix_spawn_file_actions_init(&actions);
    if (setup) {
        close(pair[0]); close(pair[1]); close(control[0]); close(control[1]); errno = setup;
        return PyErr_SetFromErrno(PyExc_OSError);
    }
    posix_spawnattr_t attributes;
    setup = posix_spawnattr_init(&attributes);
    if (setup) {
        posix_spawn_file_actions_destroy(&actions);
        close(pair[0]); close(pair[1]); close(control[0]); close(control[1]); errno = setup;
        return PyErr_SetFromErrno(PyExc_OSError);
    }
    setup = posix_spawnattr_setpgroup(&attributes, 0);
    if (!setup) setup = posix_spawnattr_setflags(&attributes, POSIX_SPAWN_SETPGROUP);
    if (!setup) setup = posix_spawn_file_actions_adddup2(&actions, pair[1], 0);
    if (!setup) setup = posix_spawn_file_actions_adddup2(&actions, pair[1], 1);
    if (!setup) setup = posix_spawn_file_actions_adddup2(&actions, control[1], 3);
    if (!setup) setup = posix_spawn_file_actions_addclosefrom_np(&actions, 4);
    pid_t child = 0;
    char *arguments[] = { host_engine, NULL };
    char *environment[] = { "PATH=/usr/bin:/bin", "LC_ALL=C", NULL };
    int started = setup ? setup : posix_spawn(&child, host_engine, &actions, &attributes,
                                             arguments, environment);
    posix_spawnattr_destroy(&attributes);
    posix_spawn_file_actions_destroy(&actions);
    close(pair[1]); close(control[1]);
    if (started) {
        close(pair[0]); close(control[0]); errno = started; return PyErr_SetFromErrno(PyExc_OSError);
    }
    struct host_stream stream = { pair[0], control[0], 0, cli, cancellation,
                                  0, HOST_VALUE_NODES, began + 3900.0 };
    unsigned char header[112] = { 'L', 'C', 'H', 'R', 'E', 'Q', '1', 0 };
    host_put32(header + 8, command); host_put32(header + 12, fault);
    for (unsigned index = 0; index < HOST_FIELDS; index++) {
        host_put32(header + 16 + 12 * index, fields[index].kind);
        host_put64(header + 20 + 12 * index, fields[index].size);
    }
    int failed = host_transfer(&stream, header, sizeof(header), 1);
    for (unsigned index = 0; !failed && index < HOST_FIELDS; index++)
        failed = host_transfer(&stream, (void *)fields[index].data, fields[index].size, 1);
    if (!failed && shutdown(stream.descriptor, SHUT_WR)) {
        PyErr_SetFromErrno(PyExc_OSError); failed = -1;
    }
    unsigned char response[24];
    if (!failed) failed = host_transfer(&stream, response, sizeof(response), 0);
    uint64_t status = 0;
    if (!failed) {
        status = host_get64(response + 8, 4);
        stream.remaining = host_get64(response + 16, 8);
        if (memcmp(response, "LCHRES1\0", 8) || status > 3 ||
            host_get64(response + 12, 4) || stream.remaining > HOST_RESPONSE_MAX) {
            PyErr_SetString(PyExc_ValueError, "invalid host response header"); failed = -1;
        }
    }
    PyObject *result = failed ? NULL : host_value(&stream, HOST_VALUE_DEPTH);
    if (result && stream.remaining) {
        PyErr_SetString(PyExc_ValueError, "trailing host value bytes"); Py_DecRef(result); result = NULL;
    }
    if (result) {
        unsigned char extra;
        for (;;) {
            if (host_ready(&stream, POLLIN)) { Py_DecRef(result); result = NULL; break; }
            ssize_t count = recv(stream.descriptor, &extra, 1, 0);
            if (count < 0 && (errno == EINTR || errno == EAGAIN || errno == EWOULDBLOCK)) continue;
            if (count != 0) {
                PyErr_SetString(PyExc_ValueError, "host response lacks exact EOF");
                Py_DecRef(result); result = NULL;
            }
            break;
        }
    }
    close(stream.descriptor); close(stream.control);
    // The complete message is evidence independently of the helper's later wait status.
    PyThreadState *saved = PyEval_SaveThread();
    host_engine_reap(child, result != NULL);
    PyEval_RestoreThread(saved);
    if (result && status) {
        host_raise(status, result);
        Py_DecRef(result); result = NULL;
    }
    return result;
}

static PyObject *host_as_path(PyObject *bytes) {
    // §FS-host-boundary.caller.initialization: Exposed classes require completed setup.
    if (!host_initialized) {
        PyErr_SetString(PyExc_RuntimeError, host_unavailable_error); return NULL;
    }
    char *data;
    Py_ssize_t size;
    if (PyBytes_AsStringAndSize(bytes, &data, &size)) return NULL;
    PyObject *text = PyUnicode_DecodeFSDefaultAndSize(data, size);
    if (!text) return NULL;
    PyObject *path = host_call_objects(host_path_class, &text, 1);
    Py_DecRef(text);
    return path;
}

static int host_has_type(PyObject *value, PyTypeObject *type, int optional) {
    if (!value) return 0;
    if (optional && value == Py_None) return 1;
    return PyObject_IsInstance(value, (PyObject *)type);
}

static PyObject *host_bundle_information(PyObject *bundle, PyObject *results) {
    struct host_field fields[HOST_FIELDS] = {{0}};
    int failed = host_field_bytes(&fields[0], bundle, 2, HOST_PATH_MAX);
    if (!failed && results) failed = host_field_bytes(&fields[1], results, 2, HOST_PATH_MAX);
    PyObject *value = failed ? NULL : host_exchange(fields, 4, 0, NULL, 0);
    for (unsigned index = 0; index < HOST_FIELDS; index++) host_field_clear(&fields[index]);
    if (!value) return NULL;
    int valid = host_has_type(value, &PyDict_Type, 0);
    if (valid > 0) valid = host_has_type(PyDict_GetItemString(value, "bundle_id"), &PyUnicode_Type, 0);
    if (valid > 0) valid = host_has_type(PyDict_GetItemString(value, "manifest"), &PyDict_Type, 0);
    if (valid <= 0) {
        Py_DecRef(value);
        if (!PyErr_Occurred()) PyErr_SetString(PyExc_ValueError, "invalid host bundle description");
        return NULL;
    }
    return value;
}

// §FS-host-boundary.caller: Parsed kwargs are borrowed until independently rooted before callbacks.
static void host_arguments_retain(PyObject *const *arguments, unsigned count) {
    for (unsigned index = 0; index < count; index++)
        if (arguments[index]) Py_IncRef(arguments[index]);
}
static void host_arguments_clear(PyObject **arguments, unsigned count) {
    for (unsigned index = 0; index < count; index++) {
        PyObject *old = arguments[index];
        arguments[index] = NULL;
        if (old) Py_DecRef(old);
    }
}

static int host_workspace_init(HostWorkspace *self, PyObject *args, PyObject *keywords) {
    // §FS-host-boundary.caller.initialization: Exposed classes require completed setup.
    if (!host_initialized) {
        PyErr_SetString(PyExc_RuntimeError, host_unavailable_error); return -1;
    }
    static char *names[] = { "bundle", "results", NULL };
    PyObject *bundle = NULL, *results = Py_None;
    PyObject **outputs[] = { &bundle, &results };
    if (!host_parse_objects(args, keywords, "|OO:Workspace", names, 2, 0, 0, outputs)) return -1;
    PyObject *arguments[] = { bundle, results };
    host_arguments_retain(arguments, 2);
    struct host_field first = {0}, second = {0};
    PyObject *default_bundle = NULL;
    if (!bundle) {
        default_bundle = PyBytes_FromStringAndSize(host_root, (Py_ssize_t)strlen(host_root));
        if (!default_bundle) { host_arguments_clear(arguments, 2); return -1; }
        bundle = default_bundle;
    }
    int failed = host_field_path(&first, bundle);
    if (default_bundle) Py_DecRef(default_bundle);
    if (!failed) failed = host_field_absolute(&first);
    if (!failed && results != Py_None) failed = host_field_path(&second, results);
    if (!failed && results != Py_None) failed = host_field_absolute(&second);
    if (!failed && results == Py_None) {
        PyObject *raw = PyBytes_FromStringAndSize(host_default_results,
                                      (Py_ssize_t)strlen(host_default_results));
        if (!raw) failed = -1;
        else { failed = host_field_bytes(&second, raw, 2, HOST_PATH_MAX); Py_DecRef(raw); }
    }
    if (failed) {
        host_field_clear(&first); host_field_clear(&second);
        host_arguments_clear(arguments, 2); return -1;
    }
    PyObject *information = host_bundle_information(first.root, second.root);
    if (!information) {
        host_field_clear(&first); host_field_clear(&second);
        host_arguments_clear(arguments, 2); return -1;
    }
    PyObject *old_bundle = self->bundle, *old_results = self->results;
    PyObject *old_information = self->information;
    self->bundle = first.root;
    self->results = second.root;
    self->information = information;
    if (old_bundle) Py_DecRef(old_bundle);
    if (old_results) Py_DecRef(old_results);
    if (old_information) Py_DecRef(old_information);
    host_arguments_clear(arguments, 2);
    return 0;
}

static void host_workspace_free(HostWorkspace *self) {
    PyObject *type = (PyObject *)Py_TYPE((PyObject *)self);
    PyObject *bundle = self->bundle, *results = self->results, *information = self->information;
    self->bundle = NULL; self->results = NULL; self->information = NULL;
    if (bundle) Py_DecRef(bundle);
    if (results) Py_DecRef(results);
    if (information) Py_DecRef(information);
    PyObject_Free(self);
    Py_DecRef(type);
}

static PyObject *host_workspace_validate(HostWorkspace *self, PyObject *args, PyObject *keywords) {
    static char *names[] = { "policy", NULL };
    PyObject *policy;
    PyObject **outputs[] = { &policy };
    if (!host_parse_objects(args, keywords, "O:validate", names, 1, 1, 0, outputs)) return NULL;
    Py_IncRef(policy);
    if (!self->bundle || !self->results || !self->information) {
        PyErr_SetString(PyExc_RuntimeError, "Workspace has not been initialized");
        Py_DecRef(policy);
        return NULL;
    }
    struct host_field fields[HOST_FIELDS] = {{0}};
    int failed = host_field_bytes(&fields[0], self->bundle, 2, HOST_PATH_MAX);
    if (!failed && self->results) failed = host_field_bytes(&fields[1], self->results, 2, HOST_PATH_MAX);
    if (!failed) failed = host_field_input(&fields[2], policy, HOST_POLICY_MAX);
    PyObject *result = failed ? NULL : host_exchange(fields, 0, 0, NULL, 0);
    for (unsigned index = 0; index < HOST_FIELDS; index++) host_field_clear(&fields[index]);
    Py_DecRef(policy);
    return result;
}

static const char *host_outcome_fields[] = {
    "request_id", "bundle_id", "command", "status", "report", "exit_code", "vm_cleanup", "error",
    "stdout", "stderr", "files", "output", "publication", "publication_error"
};

static PyObject *host_outcome_from(PyObject *data) {
    int valid = host_has_type(data, &PyDict_Type, 0);
    for (unsigned index = 0; valid > 0 && index < 14; index++) {
        PyObject *value = PyDict_GetItemString(data, host_outcome_fields[index]);
        PyTypeObject *type = index == 4 || index == 10 ? &PyDict_Type :
                             index == 5 ? &PyLong_Type : index == 8 || index == 9 ? &PyBytes_Type :
                             &PyUnicode_Type;
        valid = host_has_type(value, type, index == 4 || index == 7 || index == 11 || index == 13);
    }
    if (valid > 0) valid = host_has_type(PyDict_GetItemString(data, "json"), &PyDict_Type, 0);
    if (valid <= 0) {
        if (!PyErr_Occurred()) PyErr_SetString(PyExc_ValueError, "invalid host outcome fields");
        return NULL;
    }
    PyObject *files = PyDict_GetItemString(data, "files"), *key, *value;
    Py_ssize_t position = 0;
    while (PyDict_Next(files, &position, &key, &value)) {
        int name_type = host_has_type(key, &PyUnicode_Type, 0);
        int data_type = name_type > 0 ? host_has_type(value, &PyBytes_Type, 0) : name_type;
        if (data_type <= 0) {
            if (!PyErr_Occurred()) PyErr_SetString(PyExc_ValueError, "invalid host artifact fields");
            return NULL;
        }
    }
    PyObject *copy = PyDict_Copy(data);
    if (!copy) return NULL;
    PyObject *output = PyDict_GetItemString(copy, "output");
    if (output != Py_None) {
        PyObject *path = host_call_objects(host_path_class, &output, 1);
        if (!path) { Py_DecRef(copy); return NULL; }
        int failed = PyDict_SetItemString(copy, "output", path);
        Py_DecRef(path);
        if (failed) { Py_DecRef(copy); return NULL; }
    }
    HostOutcome *outcome = (HostOutcome *)PyType_GenericAlloc((PyTypeObject *)host_outcome_class, 0);
    if (!outcome) { Py_DecRef(copy); return NULL; }
    outcome->data = copy;
    return (PyObject *)outcome;
}

static PyObject *host_workspace_execute(HostWorkspace *self, PyObject *args, PyObject *keywords,
                                        int run) {
    static char *run_names[] = {
        "policy", "workspace", "stdin", "output", "cancellation", "timeout", "_test_fault", NULL
    };
    static char *check_names[] = {
        "policy", "workspace", "stdin", "output", "cancellation", "timeout", NULL
    };
    PyObject *policy, *workspace = Py_None, *input = Py_None, *output = Py_None;
    PyObject *cancellation = Py_None, *timeout = Py_None, *fault_value = Py_None;
    PyObject **outputs[] = { &policy, &workspace, &input, &output, &cancellation, &timeout, &fault_value };
    int parsed = run ? host_parse_objects(args, keywords, "O|$OOOOOO:run", run_names, 7, 1, 1, outputs) :
                       host_parse_objects(args, keywords, "O|$OOOOO:check", check_names, 6, 1, 1, outputs);
    if (!parsed) return NULL;
    PyObject *arguments[] = { policy, workspace, input, output, cancellation, timeout, fault_value };
    host_arguments_retain(arguments, 7);
    if (!self->bundle || !self->results || !self->information) {
        PyErr_SetString(PyExc_RuntimeError, "Workspace has not been initialized");
        host_arguments_clear(arguments, 7); return NULL;
    }
    if (cancellation != Py_None && Py_TYPE(cancellation) != (PyTypeObject *)host_cancellation_class) {
        PyErr_SetString(PyExc_TypeError, "cancellation must be a native Cancellation or None");
        host_arguments_clear(arguments, 7); return NULL;
    }
    uint32_t fault = 0;
    if (fault_value != Py_None) {
        // Real layout is required by the Unicode C API; __class__ claims are insufficient.
        int text = PyObject_TypeCheck(fault_value, &PyUnicode_Type);
        if (text < 0) { host_arguments_clear(arguments, 7); return NULL; }
        if (text && PyUnicode_CompareWithASCIIString(fault_value, "report-storage") == 0) fault = 1;
        else if (text && PyUnicode_CompareWithASCIIString(fault_value, "channel-loss") == 0) fault = 2;
        else {
            PyErr_SetString(PyExc_ValueError, "unknown acceptance fault");
            host_arguments_clear(arguments, 7); return NULL;
        }
    }
    struct host_field fields[HOST_FIELDS] = {{0}};
    int failed = host_field_bytes(&fields[0], self->bundle, 2, HOST_PATH_MAX);
    if (!failed && self->results) failed = host_field_bytes(&fields[1], self->results, 2, HOST_PATH_MAX);
    if (!failed) failed = host_field_input(&fields[2], policy, HOST_POLICY_MAX);
    if (!failed && workspace != Py_None) failed = host_field_path(&fields[3], workspace);
    if (!failed && input != Py_None) failed = host_field_input(&fields[4], input, HOST_STDIN_MAX);
    if (!failed && output != Py_None) failed = host_field_path(&fields[5], output);
    if (!failed && timeout != Py_None) {
        double seconds = PyFloat_AsDouble(timeout);
        if (PyErr_Occurred()) failed = -1;
        else if (!(seconds > 0 && seconds <= 3660)) {
            PyErr_SetString(PyExc_ValueError, "VM timeout is outside the supported bound"); failed = -1;
        } else {
            uint64_t bits; memcpy(&bits, &seconds, 8);
            fields[6].kind = 3; fields[6].size = 8; fields[6].data = (char *)fields[6].scalar;
            host_put64(fields[6].scalar, bits);
        }
    }
    PyObject *data = failed ? NULL : host_exchange(fields, run ? 2 : 1, fault,
                  cancellation == Py_None ? NULL : (HostCancellation *)cancellation, 0);
    for (unsigned index = 0; index < HOST_FIELDS; index++) host_field_clear(&fields[index]);
    host_arguments_clear(arguments, 7);
    if (!data) return NULL;
    PyObject *outcome = host_outcome_from(data);
    Py_DecRef(data);
    return outcome;
}

static PyObject *host_workspace_check(HostWorkspace *self, PyObject *args, PyObject *keywords) {
    return host_workspace_execute(self, args, keywords, 0);
}
static PyObject *host_workspace_run(HostWorkspace *self, PyObject *args, PyObject *keywords) {
    return host_workspace_execute(self, args, keywords, 1);
}

static PyObject *host_workspace_report(HostWorkspace *self, PyObject *args, PyObject *keywords) {
    static char *names[] = { "request", NULL };
    PyObject *request;
    PyObject **outputs[] = { &request };
    if (!host_parse_objects(args, keywords, "O:report", names, 1, 1, 0, outputs)) return NULL;
    Py_IncRef(request);
    if (!self->bundle || !self->results || !self->information) {
        PyErr_SetString(PyExc_RuntimeError, "Workspace has not been initialized");
        Py_DecRef(request); return NULL;
    }
    struct host_field fields[HOST_FIELDS] = {{0}};
    int failed = host_field_bytes(&fields[0], self->bundle, 2, HOST_PATH_MAX);
    if (!failed && self->results) failed = host_field_bytes(&fields[1], self->results, 2, HOST_PATH_MAX);
    if (!failed) failed = host_field_path(&fields[7], request);
    PyObject *result = failed ? NULL : host_exchange(fields, 3, 0, NULL, 0);
    for (unsigned index = 0; index < HOST_FIELDS; index++) host_field_clear(&fields[index]);
    Py_DecRef(request);
    return result;
}

static PyObject *host_workspace_get(HostWorkspace *self, void *closure) {
    uintptr_t index = (uintptr_t)closure;
    if (!self->bundle || !self->results || !self->information) {
        PyErr_SetString(PyExc_RuntimeError, "Workspace has not been initialized"); return NULL;
    }
    if (index < 2) return host_as_path(index == 0 ? self->bundle : self->results);
    PyObject *information = host_bundle_information(self->bundle, self->results);
    if (!information) return NULL;
    PyObject *value = PyDict_GetItemString(information, index == 2 ? "manifest" : "bundle_id");
    if (!value) {
        Py_DecRef(information);
        PyErr_SetString(PyExc_ValueError, "incomplete bundle description"); return NULL;
    }
    Py_IncRef(value); Py_DecRef(information); return value;
}

static int host_workspace_set(HostWorkspace *self, PyObject *value, void *closure) {
    if (!value) { PyErr_SetString(PyExc_AttributeError, "cannot delete Workspace configuration"); return -1; }
    struct host_field field = {0};
    if (host_field_path(&field, value)) return -1;
    if (host_field_absolute(&field)) { host_field_clear(&field); return -1; }
    if ((uintptr_t)closure == 0) {
        PyObject *information = host_bundle_information(field.root, self->results);
        if (!information) { host_field_clear(&field); return -1; }
        PyObject *old_bundle = self->bundle, *old_information = self->information;
        self->bundle = field.root; self->information = information;
        if (old_bundle) Py_DecRef(old_bundle);
        if (old_information) Py_DecRef(old_information);
    } else {
        PyObject *old_results = self->results;
        self->results = field.root;
        if (old_results) Py_DecRef(old_results);
    }
    return 0;
}

static int host_cancellation_init(HostCancellation *self, PyObject *args, PyObject *keywords) {
    (void)self;
    static char *names[] = { NULL };
    if (!host_parse_objects(args, keywords, ":Cancellation", names, 0, 0, 0, NULL)) return -1;
    return 0;
}
static PyObject *host_cancellation_cancel(HostCancellation *self, PyObject *unused) {
    (void)unused; self->cancelled = 1; Py_IncRef(Py_None); return Py_None;
}
static PyObject *host_cancellation_is_set(HostCancellation *self, PyObject *unused) {
    (void)unused; return PyBool_FromLong(self->cancelled != 0);
}
static PyObject *host_cancellation_event(HostCancellation *self, void *unused) {
    (void)unused; Py_IncRef((PyObject *)self); return (PyObject *)self;
}

static void host_plain_free(PyObject *self) {
    PyObject *type = (PyObject *)Py_TYPE(self); PyObject_Free(self); Py_DecRef(type);
}
// §FS-host-boundary.caller: Presentation records never enter the engine or publication path.
static int host_outcome_clear(HostOutcome *self) {
    PyObject *data = self->data;
    self->data = NULL;
    if (data) Py_DecRef(data);
    return 0;
}
static int host_outcome_traverse(HostOutcome *self, visitproc visit, void *argument) {
    return self->data ? visit(self->data, argument) : 0;
}
static void host_outcome_free(HostOutcome *self) {
    PyObject *type = (PyObject *)Py_TYPE((PyObject *)self);
    PyObject_GC_UnTrack((PyObject *)self);
    host_outcome_clear(self);
    PyObject_GC_Del(self);
    Py_DecRef(type);
}
static int host_outcome_init(HostOutcome *self, PyObject *args, PyObject *keywords) {
    static char *names[] = {
        "request_id", "bundle_id", "command", "status", "report", "exit_code", "vm_cleanup", "error",
        "stdout", "stderr", "files", "output", "publication", "publication_error", NULL
    };
    PyObject *values[14] = { NULL, NULL, NULL, NULL, NULL, NULL, NULL, Py_None,
                            NULL, NULL, NULL, Py_None, NULL, Py_None };
    PyObject **outputs[] = { &values[0], &values[1], &values[2], &values[3], &values[4], &values[5], &values[6],
                            &values[7], &values[8], &values[9], &values[10], &values[11], &values[12], &values[13] };
    if (!host_parse_objects(args, keywords, "OOOOOOO|OOOOOOO:Outcome", names, 14, 7, 0, outputs)) return -1;
    host_arguments_retain(values, 14);
    if (!values[8]) values[8] = PyBytes_FromStringAndSize("", 0);
    if (values[8] && !values[9]) values[9] = PyBytes_FromStringAndSize("", 0);
    if (values[8] && values[9] && !values[10]) values[10] = PyDict_New();
    if (values[8] && values[9] && values[10] && !values[12])
        values[12] = PyUnicode_FromString("pending");
    PyObject *data = values[8] && values[9] && values[10] && values[12] ? PyDict_New() : NULL;
    int failed = data == NULL;
    for (unsigned index = 0; !failed && index < 14; index++)
        if (PyDict_SetItemString(data, host_outcome_fields[index], values[index])) failed = 1;
    host_arguments_clear(values, 14);
    if (failed) { if (data) Py_DecRef(data); return -1; }
    PyObject *old = self->data;
    self->data = data;
    if (old) Py_DecRef(old);
    return 0;
}
static PyObject *host_outcome_get(HostOutcome *self, void *closure) {
    uintptr_t index = (uintptr_t)closure;
    if (!self->data || index >= 14) {
        PyErr_SetString(PyExc_RuntimeError, "uninitialized native Outcome"); return NULL;
    }
    PyObject *selected_data = self->data;
    Py_IncRef(selected_data);
    PyObject *value = PyDict_GetItemString(selected_data, host_outcome_fields[index]);
    if (value) Py_IncRef(value);
    Py_DecRef(selected_data);
    if (!value) { PyErr_SetString(PyExc_ValueError, "missing native Outcome field"); return NULL; }
    return value;
}
static int host_outcome_set(HostOutcome *self, PyObject *value, void *closure) {
    uintptr_t index = (uintptr_t)closure;
    if (!value) { PyErr_SetString(PyExc_AttributeError, "cannot delete an Outcome field"); return -1; }
    if (!self->data || index >= 14) {
        PyErr_SetString(PyExc_RuntimeError, "uninitialized native Outcome"); return -1;
    }
    PyObject *selected_data = self->data;
    Py_IncRef(selected_data); Py_IncRef(value);
    int result = PyDict_SetItemString(selected_data, host_outcome_fields[index], value);
    Py_DecRef(selected_data); Py_DecRef(value);
    return result;
}

// SHA256 uses the same one-operation crypto ABI as the maintained host engine.
extern unsigned char *SHA256(const unsigned char *, size_t, unsigned char *);
static PyObject *host_digest_info(PyObject *value) {
    Py_buffer view;
    if (PyObject_GetBuffer(value, &view, PyBUF_SIMPLE)) return NULL;
    if (view.len < 0) {
        PyBuffer_Release(&view); PyErr_SetString(PyExc_ValueError, "negative buffer length"); return NULL;
    }
    unsigned char digest[32];
    int success = SHA256((const unsigned char *)view.buf, (size_t)view.len, digest) != NULL;
    Py_ssize_t size = view.len;
    PyBuffer_Release(&view);
    if (!success) { PyErr_SetString(PyExc_RuntimeError, "SHA256 failed"); return NULL; }
    static const char alphabet[] = "0123456789abcdef";
    char hexadecimal[64];
    for (unsigned index = 0; index < 32; index++) {
        hexadecimal[2 * index] = alphabet[digest[index] >> 4];
        hexadecimal[2 * index + 1] = alphabet[digest[index] & 15];
    }
    PyObject *info = PyDict_New(), *amount = PyLong_FromSsize_t(size);
    PyObject *hash = PyUnicode_FromStringAndSize(hexadecimal, 64);
    int failed = !info || !amount || !hash;
    if (!failed && (PyDict_SetItemString(info, "bytes", amount) ||
                    PyDict_SetItemString(info, "sha256", hash))) failed = 1;
    if (amount) Py_DecRef(amount);
    if (hash) Py_DecRef(hash);
    if (failed) { if (info) Py_DecRef(info); return NULL; }
    return info;
}
static PyObject *host_outcome_json(HostOutcome *self, PyObject *unused) {
    (void)unused;
    if (!self->data) { PyErr_SetString(PyExc_RuntimeError, "uninitialized native Outcome"); return NULL; }
    PyObject *selected_data = self->data;
    Py_IncRef(selected_data);
    PyObject *data = PyDict_Copy(selected_data);
    Py_DecRef(selected_data);
    if (!data) return NULL;
    PyObject *result = PyDict_New(), *artifacts = PyDict_New(), *files = PyDict_New();
    PyObject *source_files = PyDict_GetItemString(data, "files");
    PyObject *file_snapshot = source_files ? PyDict_Copy(source_files) : NULL;
    PyObject *schema = PyUnicode_FromString("leancage-workspace-v1");
    PyObject *complete_string = PyUnicode_FromString("complete");
    PyObject *stdout_info = NULL, *stderr_info = NULL, *output = NULL, *complete_value = NULL;
    int failed = !result || !artifacts || !files || !file_snapshot || !schema || !complete_string;
    int complete = failed ? -1 : PyObject_RichCompareBool(
        PyDict_GetItemString(data, "status"), complete_string, Py_EQ);
    if (complete < 0) failed = 1;
    if (!failed) complete_value = PyBool_FromLong(complete);
    if (!failed && !complete_value) failed = 1;
    if (!failed) {
        stdout_info = complete ? host_digest_info(PyDict_GetItemString(data, "stdout")) : Py_None;
        if (!complete) Py_IncRef(stdout_info);
        if (!stdout_info) failed = 1;
    }
    if (!failed) {
        stderr_info = complete ? host_digest_info(PyDict_GetItemString(data, "stderr")) : Py_None;
        if (!complete) Py_IncRef(stderr_info);
        if (!stderr_info) failed = 1;
    }
    Py_ssize_t position = 0;
    PyObject *key, *value;
    while (!failed && PyDict_Next(file_snapshot, &position, &key, &value)) {
        PyObject *info = host_digest_info(value);
        if (!info) failed = 1;
        else { if (PyDict_SetItem(files, key, info)) failed = 1; Py_DecRef(info); }
    }
    if (!failed) {
        PyObject *raw_output = PyDict_GetItemString(data, "output");
        int present = PyObject_IsTrue(raw_output);
        if (present < 0) failed = 1;
        else if (present) { output = PyObject_Str(raw_output); if (!output) failed = 1; }
        else { output = Py_None; Py_IncRef(output); }
    }
    static const unsigned scalar_fields[] = { 0, 1, 2, 3, 4, 5, 6, 7, 12, 13 };
    for (unsigned index = 0; !failed && index < sizeof(scalar_fields) / sizeof(scalar_fields[0]); index++) {
        const char *name = host_outcome_fields[scalar_fields[index]];
        if (PyDict_SetItemString(result, name, PyDict_GetItemString(data, name))) failed = 1;
    }
    if (!failed && (PyDict_SetItemString(result, "schema", schema) ||
        PyDict_SetItemString(artifacts, "complete", complete_value) ||
        PyDict_SetItemString(artifacts, "stdout", stdout_info) ||
        PyDict_SetItemString(artifacts, "stderr", stderr_info) ||
        PyDict_SetItemString(artifacts, "files", files) ||
        PyDict_SetItemString(result, "output", output) ||
        PyDict_SetItemString(result, "artifacts", artifacts))) failed = 1;
    Py_DecRef(data);
    if (artifacts) Py_DecRef(artifacts);
    if (files) Py_DecRef(files);
    if (file_snapshot) Py_DecRef(file_snapshot);
    if (schema) Py_DecRef(schema);
    if (complete_string) Py_DecRef(complete_string);
    if (stdout_info) Py_DecRef(stdout_info);
    if (stderr_info) Py_DecRef(stderr_info);
    if (output) Py_DecRef(output);
    if (complete_value) Py_DecRef(complete_value);
    if (failed) { if (result) Py_DecRef(result); return NULL; }
    return result;
}

static PyObject *host_cli_item(PyObject *item) {
    PyObject *path = PyOS_FSPath(item);
    if (!path) return NULL;
    int is_bytes = PyObject_IsInstance(path, (PyObject *)&PyBytes_Type);
    if (is_bytes < 0) { Py_DecRef(path); return NULL; }
    if (is_bytes) return path;
    Py_ssize_t characters = PyUnicode_GetLength(path);
    if (characters < 0) { Py_DecRef(path); return NULL; }
    if (characters >= HOST_POLICY_MAX) {
        Py_DecRef(path); PyErr_SetString(PyExc_ValueError, "CLI argument exceeds its bound"); return NULL;
    }
    PyObject *bytes = PyUnicode_EncodeFSDefault(path);
    Py_DecRef(path);
    return bytes;
}

// §FS-host-boundary.caller: Bound iteration before copying; every item has one trailing separator.
static PyObject *host_cli_arguments(PyObject *arguments, int skip_first) {
    PyObject *iterator = PyObject_GetIter(arguments);
    if (!iterator) return NULL;
    char bytes[HOST_POLICY_MAX];
    size_t used = 0;
    if (skip_first) {
        PyObject *program = PyIter_Next(iterator);
        if (program) Py_DecRef(program);
        else if (PyErr_Occurred()) { Py_DecRef(iterator); return NULL; }
    }
    for (;;) {
        PyObject *item = PyIter_Next(iterator);
        if (!item) {
            Py_DecRef(iterator);
            if (PyErr_Occurred()) return NULL;
            return PyBytes_FromStringAndSize(bytes, (Py_ssize_t)used);
        }
        PyObject *encoded = host_cli_item(item);
        Py_DecRef(item);
        if (!encoded) { Py_DecRef(iterator); return NULL; }
        char *data;
        Py_ssize_t size;
        if (PyBytes_AsStringAndSize(encoded, &data, &size)) {
            Py_DecRef(encoded); Py_DecRef(iterator); return NULL;
        }
        if (size < 0 || used >= sizeof(bytes) || (uint64_t)size > sizeof(bytes) - used - 1 ||
            memchr(data, 0, (size_t)size)) {
            Py_DecRef(encoded); Py_DecRef(iterator);
            PyErr_SetString(PyExc_ValueError, "invalid or oversized CLI arguments"); return NULL;
        }
        memcpy(bytes + used, data, (size_t)size); used += (size_t)size;
        bytes[used++] = 0;
        Py_DecRef(encoded);
    }
}

static int host_cli_output(PyObject *bytes, const char *name) {
    PyObject *text_stream = PySys_GetObject(name);
    if (!text_stream) { PyErr_SetString(PyExc_RuntimeError, "public output stream unavailable"); return -1; }
    Py_IncRef(text_stream);
    PyObject *stream = PyObject_GetAttrString(text_stream, "buffer");
    int text_mode = 0;
    if (!stream) {
        if (!PyErr_ExceptionMatches(PyExc_AttributeError)) { Py_DecRef(text_stream); return -1; }
        PyErr_Clear(); stream = text_stream; text_mode = 1;
    } else Py_DecRef(text_stream);
    char *data;
    Py_ssize_t size;
    if (PyBytes_AsStringAndSize(bytes, &data, &size)) { Py_DecRef(stream); return -1; }
    if (size < 0 || size > 4194305) {
        Py_DecRef(stream); PyErr_SetString(PyExc_ValueError, "public CLI output exceeds its bound"); return -1;
    }
    PyObject *write_name = PyUnicode_FromString("write");
    if (!write_name) { Py_DecRef(stream); return -1; }
    Py_ssize_t offset = 0;
    while (offset < size) {
        PyObject *part = text_mode ? PyUnicode_DecodeUTF8(data + offset, size - offset, "strict") :
                                    PyBytes_FromStringAndSize(data + offset, size - offset);
        if (!part) { Py_DecRef(write_name); Py_DecRef(stream); return -1; }
        Py_ssize_t expected = text_mode ? PyUnicode_GetLength(part) : size - offset;
        if (expected < 0) { Py_DecRef(part); Py_DecRef(write_name); Py_DecRef(stream); return -1; }
        PyObject *method = PyObject_GetAttr(stream, write_name);
        PyObject *returned = method ? host_call_objects(method, &part, 1) : NULL;
        if (method) Py_DecRef(method);
        Py_DecRef(part);
        if (!returned) { Py_DecRef(write_name); Py_DecRef(stream); return -1; }
        Py_ssize_t count = PyLong_AsSsize_t(returned);
        Py_DecRef(returned);
        if (count == -1 && PyErr_Occurred()) { Py_DecRef(write_name); Py_DecRef(stream); return -1; }
        if (count <= 0 || count > expected || (text_mode && count != expected)) {
            Py_DecRef(write_name); Py_DecRef(stream);
            PyErr_SetString(PyExc_OSError, "partial public CLI output"); return -1;
        }
        offset = text_mode ? size : offset + count;
    }
    Py_DecRef(write_name);
    PyObject *flush_name = PyUnicode_FromString("flush");
    if (!flush_name) { Py_DecRef(stream); return -1; }
    PyObject *method = PyObject_GetAttr(stream, flush_name);
    PyObject *flushed = method ? PyObject_CallObject(method, NULL) : NULL;
    if (method) Py_DecRef(method);
    Py_DecRef(flush_name); Py_DecRef(stream);
    if (!flushed) return -1;
    Py_DecRef(flushed);
    return 0;
}

static PyObject *host_cli_call(PyObject *module, PyObject *args, PyObject *keywords) {
    (void)module;
    static char *names[] = { "argv", NULL };
    PyObject *arguments = Py_None;
    PyObject **outputs[] = { &arguments };
    if (!host_parse_objects(args, keywords, "|O:cli", names, 1, 0, 0, outputs)) return NULL;
    int system_arguments = arguments == Py_None;
    if (system_arguments) {
        arguments = PySys_GetObject("argv");
        if (!arguments) { PyErr_SetString(PyExc_RuntimeError, "CLI arguments unavailable"); return NULL; }
    }
    Py_IncRef(arguments);
    PyObject *raw = host_cli_arguments(arguments, system_arguments);
    Py_DecRef(arguments);
    if (!raw) return NULL;
    PyObject *bundle = PyBytes_FromStringAndSize(host_root, (Py_ssize_t)strlen(host_root));
    if (!bundle) { Py_DecRef(raw); return NULL; }
    PyObject *results = PyBytes_FromStringAndSize(host_default_results,
                                                (Py_ssize_t)strlen(host_default_results));
    if (!results) { Py_DecRef(bundle); Py_DecRef(raw); return NULL; }
    struct host_field fields[HOST_FIELDS] = {{0}};
    int failed = host_field_bytes(&fields[0], bundle, 2, HOST_PATH_MAX);
    if (!failed) failed = host_field_bytes(&fields[1], results, 2, HOST_PATH_MAX);
    if (!failed) failed = host_field_bytes(&fields[2], raw, 1, HOST_POLICY_MAX);
    Py_DecRef(bundle); Py_DecRef(results); Py_DecRef(raw);
    PyObject *result = failed ? NULL : host_exchange(fields, 5, 0, NULL, 1);
    for (unsigned index = 0; index < HOST_FIELDS; index++) host_field_clear(&fields[index]);
    if (!result) return NULL;
    int object = PyObject_IsInstance(result, (PyObject *)&PyDict_Type);
    if (object <= 0) {
        Py_DecRef(result);
        if (!PyErr_Occurred()) PyErr_SetString(PyExc_ValueError, "invalid CLI response");
        return NULL;
    }
    PyObject *code = PyDict_GetItemString(result, "exit_code");
    PyObject *output = PyDict_GetItemString(result, "stdout");
    PyObject *error_output = PyDict_GetItemString(result, "stderr");
    if (!code || !output) {
        Py_DecRef(result); PyErr_SetString(PyExc_ValueError, "incomplete CLI response"); return NULL;
    }
    long exit_code = PyLong_AsLong(code);
    if (exit_code == -1 && PyErr_Occurred()) { Py_DecRef(result); return NULL; }
    if (exit_code < 0 || exit_code > 255) {
        Py_DecRef(result); PyErr_SetString(PyExc_ValueError, "invalid CLI exit status"); return NULL;
    }
    if (host_cli_output(output, "stdout") || (error_output && host_cli_output(error_output, "stderr"))) {
        Py_DecRef(result); return NULL;
    }
    PyObject *status = PyLong_FromLong(exit_code);
    Py_DecRef(result);
    return status;
}

static void host_cli_signal(int number) { (void)number; host_cli_cancelled = 1; }

// §FS-host-boundary.caller: The CLI owns and restores its signal handlers on every returned path.
static PyObject *host_cli(PyObject *module, PyObject *args, PyObject *keywords) {
    // §FS-host-boundary.caller.initialization: Exposed classes require completed setup.
    if (!host_initialized) {
        PyErr_SetString(PyExc_RuntimeError, host_unavailable_error); return NULL;
    }
    if (host_cli_active) {
        PyErr_SetString(PyExc_RuntimeError, "a native CLI call is already active"); return NULL;
    }
    host_cli_cancelled = 0;
    struct sigaction action, old_interrupt, old_terminate;
    memset(&action, 0, sizeof(action));
    action.sa_handler = host_cli_signal;
    if (sigemptyset(&action.sa_mask)) return PyErr_SetFromErrno(PyExc_OSError);
    if (sigaction(SIGINT, &action, &old_interrupt)) return PyErr_SetFromErrno(PyExc_OSError);
    if (sigaction(SIGTERM, &action, &old_terminate)) {
        int number = errno; sigaction(SIGINT, &old_interrupt, NULL); errno = number;
        return PyErr_SetFromErrno(PyExc_OSError);
    }
    host_cli_active = 1;
    PyObject *result = host_cli_call(module, args, keywords);
    int first = sigaction(SIGINT, &old_interrupt, NULL), first_errno = errno;
    int second = sigaction(SIGTERM, &old_terminate, NULL), second_errno = errno;
    host_cli_active = 0;
    if (result && (first || second)) {
        Py_DecRef(result); errno = first ? first_errno : second_errno;
        return PyErr_SetFromErrno(PyExc_OSError);
    }
    return result;
}

static PyMethodDef host_workspace_methods[] = {
    { "validate", (PyCFunction)(void (*)(void))host_workspace_validate, METH_VARARGS | METH_KEYWORDS,
      "Validate the exact bounded caller policy in the identified host engine." },
    { "check", (PyCFunction)(void (*)(void))host_workspace_check, METH_VARARGS | METH_KEYWORDS,
      "Check entry and filesystem authority in the owned disposable VM." },
    { "run", (PyCFunction)(void (*)(void))host_workspace_run, METH_VARARGS | METH_KEYWORDS,
      "Execute a bounded policy in the owned disposable VM and return its observations." },
    { "report", (PyCFunction)(void (*)(void))host_workspace_report, METH_VARARGS | METH_KEYWORDS,
      "Retrieve the bounded validated metadata of one published result." },
    { NULL, NULL, 0, NULL }
};
static PyGetSetDef host_workspace_properties[] = {
    { "bundle", (getter)host_workspace_get, (setter)host_workspace_set, "Absolute selected bundle.", (void *)0 },
    { "results", (getter)host_workspace_get, (setter)host_workspace_set, "Absolute result parent.", (void *)1 },
    { "manifest", (getter)host_workspace_get, NULL, "Identified bundle manifest.", (void *)2 },
    { "bundle_id", (getter)host_workspace_get, NULL, "Identified bundle digest.", (void *)3 },
    { NULL, NULL, NULL, NULL, NULL }
};
static PyType_Slot host_workspace_slots[] = {
    { Py_tp_new, (void *)PyType_GenericNew },
    { Py_tp_init, (void *)host_workspace_init },
    { Py_tp_dealloc, (void *)host_workspace_free },
    { Py_tp_methods, (void *)host_workspace_methods },
    { Py_tp_getset, (void *)host_workspace_properties },
    { 0, NULL }
};
static PyType_Spec host_workspace_spec = {
    "leancage._host.Workspace", sizeof(HostWorkspace), 0, Py_TPFLAGS_DEFAULT, host_workspace_slots
};
static PyMethodDef host_cancellation_methods[] = {
    { "cancel", (PyCFunction)host_cancellation_cancel, METH_NOARGS, "Request cancellation, once." },
    { "is_set", (PyCFunction)host_cancellation_is_set, METH_NOARGS, "Return the sticky request flag." },
    { NULL, NULL, 0, NULL }
};
static PyGetSetDef host_cancellation_properties[] = {
    { "event", (getter)host_cancellation_event, NULL, "Compatibility view of the request flag.", NULL },
    { NULL, NULL, NULL, NULL, NULL }
};
static PyType_Slot host_cancellation_slots[] = {
    { Py_tp_new, (void *)PyType_GenericNew }, { Py_tp_init, (void *)host_cancellation_init },
    { Py_tp_dealloc, (void *)host_plain_free }, { Py_tp_methods, (void *)host_cancellation_methods },
    { Py_tp_getset, (void *)host_cancellation_properties }, { 0, NULL }
};
static PyType_Spec host_cancellation_spec = {
    "leancage._host.Cancellation", sizeof(HostCancellation), 0, Py_TPFLAGS_DEFAULT, host_cancellation_slots
};
static PyMethodDef host_outcome_methods[] = {
    { "json", (PyCFunction)host_outcome_json, METH_NOARGS, "Return the public JSON envelope." },
    { NULL, NULL, 0, NULL }
};
static PyGetSetDef host_outcome_properties[] = {
    { "request_id", (getter)host_outcome_get, (setter)host_outcome_set, NULL, (void *)0 },
    { "bundle_id", (getter)host_outcome_get, (setter)host_outcome_set, NULL, (void *)1 },
    { "command", (getter)host_outcome_get, (setter)host_outcome_set, NULL, (void *)2 },
    { "status", (getter)host_outcome_get, (setter)host_outcome_set, NULL, (void *)3 },
    { "report", (getter)host_outcome_get, (setter)host_outcome_set, NULL, (void *)4 },
    { "exit_code", (getter)host_outcome_get, (setter)host_outcome_set, NULL, (void *)5 },
    { "vm_cleanup", (getter)host_outcome_get, (setter)host_outcome_set, NULL, (void *)6 },
    { "error", (getter)host_outcome_get, (setter)host_outcome_set, NULL, (void *)7 },
    { "stdout", (getter)host_outcome_get, (setter)host_outcome_set, NULL, (void *)8 },
    { "stderr", (getter)host_outcome_get, (setter)host_outcome_set, NULL, (void *)9 },
    { "files", (getter)host_outcome_get, (setter)host_outcome_set, NULL, (void *)10 },
    { "output", (getter)host_outcome_get, (setter)host_outcome_set, NULL, (void *)11 },
    { "publication", (getter)host_outcome_get, (setter)host_outcome_set, NULL, (void *)12 },
    { "publication_error", (getter)host_outcome_get, (setter)host_outcome_set, NULL, (void *)13 },
    { host_observation_name, (getter)host_outcome_observation, NULL, NULL, NULL },
    { NULL, NULL, NULL, NULL, NULL }
};
static PyType_Slot host_outcome_slots[] = {
    { Py_tp_new, (void *)PyType_GenericNew }, { Py_tp_init, (void *)host_outcome_init },
    { Py_tp_dealloc, (void *)host_outcome_free }, { Py_tp_traverse, (void *)host_outcome_traverse },
    { Py_tp_clear, (void *)host_outcome_clear },
    { Py_tp_methods, (void *)host_outcome_methods }, { Py_tp_getset, (void *)host_outcome_properties },
    { 0, NULL }
};
static PyType_Spec host_outcome_spec = {
    "leancage._host.Outcome", sizeof(HostOutcome), 0,
    (Py_TPFLAGS_DEFAULT | Py_TPFLAGS_HAVE_GC | Py_TPFLAGS_IMMUTABLETYPE), host_outcome_slots
};
static PyMethodDef host_module_methods[] = {
    { "cli", (PyCFunction)(void (*)(void))host_cli, METH_VARARGS | METH_KEYWORDS,
      "Execute the same bounded host request through the public command syntax." },
    { NULL, NULL, 0, NULL }
};
static PyModuleDef host_module = {
    PyModuleDef_HEAD_INIT, "_host", "Native gateway to the source-connected Lean host engine.",
    -1, host_module_methods, NULL, NULL, NULL, NULL
};

static int host_initializing = 0;
static int host_initialized = 0;
static const char host_initialization_error[51];
static const char host_initialized_error[36];
static const char host_interpreter_error[53];

static PyObject *host_initialize(void) {
    if (PyInterpreterState_GetID(PyInterpreterState_Get()) != 0) {
        PyErr_SetString(PyExc_ImportError, "host gateway requires the supported main interpreter");
        return NULL;
    }
    if (host_bootstrap()) {
        PyErr_SetString(PyExc_ImportError, "host extension is outside its identified bootstrap layout");
        return NULL;
    }
    PyObject *pathlib = PyImport_ImportModule("pathlib");
    if (!pathlib) return NULL;
    host_path_class = PyObject_GetAttrString(pathlib, "Path");
    Py_DecRef(pathlib);
    if (!host_path_class) return NULL;
    PyObject *module = PyModule_Create(&host_module);
    if (!module) return NULL;
    PyObject *workspace = PyType_FromSpec(&host_workspace_spec);
    if (!workspace) { Py_DecRef(module); return NULL; }
    if (PyModule_AddObject(module, "Workspace", workspace)) {
        Py_DecRef(workspace); Py_DecRef(module); return NULL;
    }
    host_cancellation_class = PyType_FromSpec(&host_cancellation_spec);
    if (!host_cancellation_class) { Py_DecRef(module); return NULL; }
    if (PyModule_AddObjectRef(module, "Cancellation", host_cancellation_class)) {
        Py_DecRef(module); return NULL;
    }
    host_outcome_class = PyType_FromSpec(&host_outcome_spec);
    if (!host_outcome_class) { Py_DecRef(module); return NULL; }
    if (PyModule_AddObjectRef(module, "Outcome", host_outcome_class)) {
        Py_DecRef(module); return NULL;
    }
    return module;
}

// §FS-host-boundary.caller.initialization: Reentry cannot replace live initializer globals.
PyMODINIT_FUNC PyInit__host(void) {
    if (PyInterpreterState_GetID(PyInterpreterState_Get()) != 0) {
        PyErr_SetString(PyExc_ImportError, host_interpreter_error);
        return NULL;
    }
    if (host_initializing) {
        PyErr_SetString(PyExc_ImportError, host_initialization_error);
        return NULL;
    }
    if (host_initialized) {
        PyErr_SetString(PyExc_ImportError, host_initialized_error);
        return NULL;
    }
    host_initializing = 1;
    PyObject *result = host_initialize();
    if (result) host_initialized = 1;
    host_initializing = 0;
    return result;
}
// §FS-host-boundary.caller: Fixed-signature object parsing has executable source semantics.
static int host_parse_objects(PyObject *args, PyObject *keywords, const char *format,
                              char *const *names, unsigned count, unsigned required,
                              int keyword_only, PyObject ***outputs) {
    (void)format;
    if (count > 14 || required > count) {
        PyErr_SetString(PyExc_SystemError, "invalid native argument table"); return 0;
    }
    Py_ssize_t positional = PyTuple_Size(args);
    if (positional < 0) return 0;
    unsigned maximum = keyword_only ? required : count;
    if ((uint64_t)positional > maximum) {
        PyErr_SetString(PyExc_TypeError, "too many positional arguments"); return 0;
    }
    unsigned char seen[14] = {0};
    for (unsigned index = 0; index < (unsigned)positional; index++) {
        PyObject *value = PyTuple_GetItem(args, index);
        if (!value) return 0;
        *outputs[index] = value; seen[index] = 1;
    }
    if (keywords) {
        Py_ssize_t position = 0;
        PyObject *key, *value;
        while (PyDict_Next(keywords, &position, &key, &value)) {
            if (!PyObject_TypeCheck(key, &PyUnicode_Type)) {
                PyErr_SetString(PyExc_TypeError, "keywords must be strings"); return 0;
            }
            unsigned index;
            for (index = 0; index < count; index++) {
                int compared = PyUnicode_CompareWithASCIIString(key, names[index]);
                if (compared == 0) break;
                if (compared < 0 && PyErr_Occurred()) return 0;
            }
            if (index == count) {
                PyErr_SetString(PyExc_TypeError, "unexpected keyword argument"); return 0;
            }
            if (seen[index]) {
                PyErr_SetString(PyExc_TypeError, "argument has multiple values"); return 0;
            }
            *outputs[index] = value; seen[index] = 1;
        }
    }
    for (unsigned index = 0; index < required; index++) {
        if (!seen[index]) {
            PyErr_SetString(PyExc_TypeError, "missing required argument"); return 0;
        }
    }
    return 1;
}

// §FS-host-boundary.caller: Callback arguments are rooted in a fresh tuple before the call.
static PyObject *host_call_objects(PyObject *callable, PyObject *const *values, unsigned count) {
    if (count > 3) {
        PyErr_SetString(PyExc_SystemError, "native call argument count exceeds its bound"); return NULL;
    }
    PyObject *arguments = PyTuple_New(count);
    if (!arguments) return NULL;
    for (unsigned index = 0; index < count; index++) {
        Py_IncRef(values[index]);
        if (PyTuple_SetItem(arguments, index, values[index])) {
            Py_DecRef(arguments); return NULL;
        }
    }
    PyObject *result = PyObject_CallObject(callable, arguments);
    Py_DecRef(arguments);
    return result;
}

// §FS-host-boundary.caller: Keep engine observations separate from presentation callbacks.
static const char host_observation_name[12] = "observation";
static PyObject *host_outcome_observation(HostOutcome *self, void *unused) {
    (void)unused;
    if (!self->data) {
        PyErr_SetString(PyExc_RuntimeError, "uninitialized native Outcome"); return NULL;
    }
    PyObject *selected_data = self->data;
    Py_IncRef(selected_data);
    PyObject *value = PyDict_GetItemString(selected_data, "json");
    if (!value && PyErr_Occurred()) { Py_DecRef(selected_data); return NULL; }
    if (!value) value = Py_None;
    Py_IncRef(value);
    Py_DecRef(selected_data);
    return value;
}

static const char host_initialization_error[51] = "host gateway initialization is already in progress";
static const char host_initialized_error[36] = "host gateway is already initialized";
static const char host_interpreter_error[53] = "host gateway requires the supported main interpreter";

static const char host_unavailable_error[32] = "host gateway is not initialized";
