// SPDX-License-Identifier: Apache-2.0
// §AR-metadata.primitives: One operation per dispatch; the application owns ordering and handles.
#define _GNU_SOURCE
#include <lean/lean.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <stdint.h>
#include <string.h>
#include <sys/syscall.h>
#include <unistd.h>

_Static_assert(sizeof(void *) == 8 && sizeof(long) == 8 && sizeof(size_t) == 8,
    "Linux x86-64 LP64 metadata ABI");
_Static_assert(sizeof(int) == 4, "Linux descriptor width");

static lean_object *metadata_reply(long value, int error, const unsigned char *data, size_t count) {
    uint64_t encoded = value < 0 ? (uint64_t)-(error > 0 && error <= 4095 ? error : EIO) : (uint64_t)value;
    lean_object *bytes = lean_alloc_sarray(1, count, count);
    if (count) memcpy(lean_sarray_cptr(bytes), data, count);
    lean_object *reply = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(reply, 0, lean_box_uint64(encoded));
    lean_ctor_set(reply, 1, bytes);
    return reply;
}

LEAN_EXPORT lean_obj_res leancage_metadata_primitive(uint32_t op, uint32_t fd,
    uint64_t amount, b_lean_obj_arg path) {
    unsigned char buffer[4096] = {0};
    long value = -1;
    size_t count = 0;
    switch (op) {
    case 0:
        value = syscall(SYS_openat, AT_FDCWD, lean_string_cstr(path), O_RDONLY | O_CLOEXEC, 0);
        break;
    case 1:
        if (fd > INT_MAX || amount < 1 || amount > sizeof(buffer)) { errno = EINVAL; break; }
        value = syscall(SYS_read, (int)fd, buffer, (size_t)amount);
        if (value >= 0 && (uint64_t)value <= amount) count = (size_t)value;
        break;
    case 2:
        if (fd > INT_MAX) { errno = EBADF; break; }
        value = syscall(SYS_close, (int)fd);
        break;
    default:
        errno = EINVAL;
        break;
    }
    int error = errno;
    return metadata_reply(value, error, buffer, count);
}
