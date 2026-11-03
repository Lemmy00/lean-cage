// SPDX-License-Identifier: Apache-2.0
// §AR-entry.effects: Each dispatch performs one named primitive, never an admission sequence.
#define _GNU_SOURCE
#include <lean/lean.h>
#include <errno.h>
#include <fcntl.h>
#include <linux/capability.h>
#include <linux/filter.h>
#include <linux/seccomp.h>
#include <pthread.h>
#include <signal.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/prctl.h>
#include <sys/ptrace.h>
#include <sys/syscall.h>
#include <time.h>
#include <unistd.h>

_Static_assert(sizeof(void *) == 8 && sizeof(long) == 8, "Linux x86-64 LP64");
_Static_assert(sizeof(uid_t) == 4 && sizeof(gid_t) == 4, "Linux IDs");
_Static_assert(sizeof(struct sock_filter) == 8 && sizeof(struct sock_fprog) == 16, "BPF ABI");
_Static_assert(offsetof(struct sock_filter, k) == 4 && offsetof(struct sock_fprog, filter) == 8,
    "BPF field offsets");
_Static_assert(__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__, "little-endian ABI");

// §FS-entry.runtime: Dedicated runtime startup; the worker does not use task or libuv APIs.
void __wrap_initialize_libuv(void) {}
void __wrap_lean_init_task_manager(void) {}
lean_object *__wrap_lean_run_main(lean_object *(*fn)(int, char **), int argc, char **argv) {
    return fn(argc, argv);
}
int __wrap_pthread_create(pthread_t *thread, const pthread_attr_t *attributes,
    void *(*fn)(void *), void *arg) {
    (void)thread; (void)attributes; (void)fn; (void)arg;
    return EAGAIN;
}

static lean_object *reply(long value, const unsigned char *data, size_t size) {
    uint64_t encoded = value < 0 ? (uint64_t)-(errno > 0 && errno <= 4095 ? errno : EIO) : (uint64_t)value;
    lean_object *bytes = lean_alloc_sarray(1, size, size);
    if (size) memcpy(lean_sarray_cptr(bytes), data, size);
    lean_object *pair = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(pair, 0, lean_box_uint64(encoded));
    lean_ctor_set(pair, 1, bytes);
    return pair;
}

LEAN_EXPORT lean_obj_res leancage_entry_primitive(uint32_t op, uint64_t a, uint64_t b,
    uint64_t c, b_lean_obj_arg text, b_lean_obj_arg args, b_lean_obj_arg data) {
    long value = -1;
    unsigned char output[24] = {0}; size_t used = 0;
    switch (op) {
    case 0: value = syscall(SYS_rt_sigprocmask, SIG_SETMASK, &a, NULL, 8); break;
    case 1: {
        struct { uintptr_t handler, flags, restorer; uint64_t mask; } action = {0};
        value = syscall(SYS_rt_sigaction, a, &action, NULL, 8); break;
    }
    case 2: value = ptrace(PTRACE_TRACEME, 0, NULL, NULL); break;
    case 3: value = raise(SIGSTOP); break;
    case 4: value = syscall(SYS_dup2, a, b); break;
    case 5: value = syscall(SYS_dup3, a, b, c); break;
    case 6: value = syscall(SYS_close_range, a, b, c); break;
    case 7: value = syscall(SYS_chroot, lean_string_cstr(text)); break;
    case 8: value = syscall(SYS_chdir, lean_string_cstr(text)); break;
    case 9: value = syscall(SYS_setsid); break;
    case 10: value = syscall(SYS_umask, a); break;
    case 11: value = prctl((int)a, (unsigned long)b, (unsigned long)c, 0UL, 0UL); break;
    case 12: value = syscall(SYS_setgroups, 0, NULL); break;
    case 13: value = syscall(SYS_setresgid, a, b, c); break;
    case 14: value = syscall(SYS_setresuid, a, b, c); break;
    case 15: {
        struct __user_cap_header_struct header = {_LINUX_CAPABILITY_VERSION_3, 0};
        struct __user_cap_data_struct caps[2] = {{0}, {0}};
        value = syscall(SYS_capset, &header, caps); break;
    }
    case 16: {
        struct __user_cap_header_struct header = {_LINUX_CAPABILITY_VERSION_3, 0};
        value = syscall(SYS_capget, &header, output); used = value == 0 ? 24 : 0; break;
    }
    case 17: value = syscall(SYS_getresuid, output, output + 4, output + 8); used = value == 0 ? 12 : 0; break;
    case 18: value = syscall(SYS_getresgid, output, output + 4, output + 8); used = value == 0 ? 12 : 0; break;
    case 19: value = syscall(SYS_getgroups, 0, NULL); break;
    case 20: value = syscall(SYS_setfsuid, a); break;
    case 21: value = syscall(SYS_setfsgid, a); break;
    case 22: {
        size_t size = lean_sarray_size(data);
        if (size % 8 || size > 4096 * 8) { errno = EINVAL; break; }
        struct sock_filter filter[4096];
        if (size) memcpy(filter, lean_sarray_cptr(data), size);
        struct sock_fprog program = {(unsigned short)(size / 8), filter};
        value = prctl(PR_SET_SECCOMP, SECCOMP_MODE_FILTER, &program, 0UL, 0UL); break;
    }
    case 23: {
        size_t count = lean_array_size(args), size = lean_sarray_size(data), offset = 0;
        char *argv[65], *env[9];
        if (count < 1 || count > 64 || size > 4096) { errno = E2BIG; break; }
        for (size_t i = 0; i < count; i++) argv[i] = (char *)lean_string_cstr(lean_array_uget_borrowed(args, i));
        argv[count] = NULL;
        for (size_t i = 0; i < 8; i++) {
            if (offset >= size) { errno = EINVAL; goto done; }
            env[i] = (char *)lean_sarray_cptr(data) + offset;
            const char *end = memchr(env[i], 0, size - offset);
            if (!end) { errno = EINVAL; goto done; }
            offset += (size_t)(end - env[i]) + 1;
        }
        if (offset != size) { errno = EINVAL; break; }
        env[8] = NULL;
        value = syscall(SYS_execve, lean_string_cstr(text), argv, env); break;
    }
    case 24: value = syscall(SYS_write, a, lean_sarray_cptr(data), lean_sarray_size(data)); break;
    case 25: value = syscall(SYS_exit_group, a); break;
    case 26: {
        struct timespec time = {(time_t)(a / 1000), (long)(a % 1000) * 1000000};
        value = syscall(SYS_nanosleep, &time, NULL); break;
    }
    default: errno = EINVAL; break;
    }
done:
    return reply(value, output, used);
}
