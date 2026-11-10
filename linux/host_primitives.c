// SPDX-License-Identifier: Apache-2.0
// §AR-host-boundary.interfaces: Individual effects expose exact arguments and returned bytes.
#define _GNU_SOURCE
#include <lean/lean.h>
#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <linux/fs.h>
#include <linux/stat.h>
#include <poll.h>
#include <signal.h>
#include <stddef.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/ioctl.h>
#include <sys/socket.h>
#include <sys/syscall.h>
#include <sys/un.h>
#include <sys/xattr.h>
#include <sys/vfs.h>
#include <time.h>
#include <unistd.h>

_Static_assert(sizeof(void *) == 8 && sizeof(long) == 8 && sizeof(size_t) == 8,
    "Linux x86-64 LP64 host ABI");
_Static_assert(sizeof(int) == 4, "Linux descriptor ABI");

/* SHA256 is the existing host crypto runtime primitive, not application control. */
extern unsigned char *SHA256(const unsigned char *, size_t, unsigned char *);
struct evp_md_st;
extern const struct evp_md_st *EVP_sha256(void);
extern unsigned char *HMAC(const struct evp_md_st *, const void *, int,
    const unsigned char *, size_t, unsigned char *, unsigned int *);
extern int CRYPTO_memcmp(const void *, const void *, size_t);

static lean_object *host_reply(long value, int error, const unsigned char *data, size_t count) {
    uint64_t encoded = value < 0 ? (uint64_t)-(error > 0 && error <= 4095 ? error : EIO) : (uint64_t)value;
    lean_object *bytes = lean_alloc_sarray(1, count, count);
    if (count) memcpy(lean_sarray_cptr(bytes), data, count);
    lean_object *reply = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(reply, 0, lean_box_uint64(encoded));
    lean_ctor_set(reply, 1, bytes);
    return reply;
}

static int host_path(b_lean_obj_arg bytes) {
    size_t size = lean_sarray_size(bytes);
    const unsigned char *data = lean_sarray_cptr(bytes);
    return size >= 1 && size <= 4096 && data[size-1] == 0 && !memchr(data, 0, size-1);
}

static int host_fd(uint64_t fd) { return fd <= INT_MAX; }
static int host_dirfd(uint64_t fd) { return host_fd(fd) || fd == (uint64_t)(int64_t)AT_FDCWD; }
static int host_dir(uint64_t fd) { return fd == (uint64_t)(int64_t)AT_FDCWD ? AT_FDCWD : (int)fd; }

static void host_word(unsigned char *target, uint64_t value) {
    for (size_t i = 0; i < 8; i++) target[i] = (unsigned char)(value >> (8*i));
}

LEAN_EXPORT lean_obj_res leancage_host_primitive(uint32_t op, uint64_t first,
    uint64_t second, uint64_t third, b_lean_obj_arg left, b_lean_obj_arg right) {
    unsigned char buffer[65536] = {0};
    long value = -1;
    size_t count = 0;
    errno = 0;
    switch (op) {
    case 0:
        if (!host_dirfd(first) || second > INT_MAX || third > 07777 || !host_path(left)) { errno = EINVAL; break; }
        value = syscall(SYS_openat, host_dir(first), lean_sarray_cptr(left), (int)second, (mode_t)third);
        break;
    case 1:
        if (!host_fd(first) || second < 1 || second > sizeof(buffer)) { errno = EINVAL; break; }
        value = syscall(SYS_read, (int)first, buffer, (size_t)second);
        if (value >= 0 && (uint64_t)value <= second) count = (size_t)value;
        break;
    case 2:
        if (!host_fd(first) || lean_sarray_size(left) > sizeof(buffer)) { errno = EINVAL; break; }
        value = syscall(SYS_write, (int)first, lean_sarray_cptr(left), lean_sarray_size(left));
        break;
    case 3:
        if (!host_fd(first)) { errno = EBADF; break; }
        value = syscall(SYS_close, (int)first);
        break;
    case 4: {
        struct stat information = {0};
        if (!host_fd(first)) { errno = EBADF; break; }
        value = syscall(SYS_fstat, (int)first, &information);
        if (value == 0) {
            const uint64_t words[] = {information.st_dev, information.st_ino, information.st_mode,
                information.st_nlink, information.st_uid, information.st_gid, (uint64_t)information.st_size,
                (uint64_t)information.st_mtim.tv_sec, (uint64_t)information.st_mtim.tv_nsec,
                (uint64_t)information.st_ctim.tv_sec, (uint64_t)information.st_ctim.tv_nsec};
            for (size_t i = 0; i < sizeof(words)/sizeof(words[0]); i++) host_word(buffer+8*i, words[i]);
            count = sizeof(words);
        }
        break;
    }
    case 5:
        if (!host_dirfd(first) || second > 07777 || !host_path(left)) { errno = EINVAL; break; }
        value = syscall(SYS_mkdirat, host_dir(first), lean_sarray_cptr(left), (mode_t)second);
        break;
    case 6:
        if (!host_fd(first) || !host_fd(second) || !host_path(left) || !host_path(right)) { errno = EINVAL; break; }
        value = syscall(SYS_renameat2, (int)first, lean_sarray_cptr(left), (int)second, lean_sarray_cptr(right), 1);
        break;
    case 7:
        if (!host_dirfd(first) || (second != 0 && second != AT_REMOVEDIR) || !host_path(left)) { errno = EINVAL; break; }
        value = syscall(SYS_unlinkat, host_dir(first), lean_sarray_cptr(left), (int)second);
        break;
    case 8:
        if (first < 1 || first > sizeof(buffer)) { errno = EINVAL; break; }
        value = syscall(SYS_getrandom, buffer, (size_t)first, 0);
        if (value >= 0 && (uint64_t)value <= first) count = (size_t)value;
        break;
    case 9: {
        if (!host_fd(first)) { errno = EBADF; break; }
        DIR *directory = fdopendir((int)first);
        if (directory) { host_word(buffer, (uint64_t)(uintptr_t)directory); value = 0; count = 8; }
        break;
    }
    case 10: {
        if (!first) { errno = EINVAL; break; }
        struct dirent *entry = readdir((DIR *)(uintptr_t)first);
        if (entry) {
            count = strnlen(entry->d_name, 256);
            if (!count || count > 255) { errno = EIO; count = 0; break; }
            memcpy(buffer, entry->d_name, count); value = 1;
        } else if (!errno) value = 0;
        break;
    }
    case 11:
        if (!first) { errno = EINVAL; break; }
        value = closedir((DIR *)(uintptr_t)first);
        break;
    case 12:
        if (SHA256(lean_sarray_cptr(left), lean_sarray_size(left), buffer)) { value = 0; count = 32; }
        else errno = EIO;
        break;
    case 13: {
        struct timespec observed = {0};
        value = clock_gettime(CLOCK_MONOTONIC, &observed);
        if (value == 0) {
            host_word(buffer, (uint64_t)observed.tv_sec); host_word(buffer+8, (uint64_t)observed.tv_nsec);
            count = 16;
        }
        break;
    }
    case 14: {
        char temporary[4096];
        if (!host_path(left) || lean_sarray_size(left) < 7) { errno = EINVAL; break; }
        memcpy(temporary, lean_sarray_cptr(left), lean_sarray_size(left));
        if (mkdtemp(temporary)) {
            count = strlen(temporary); memcpy(buffer, temporary, count); value = 0;
        }
        break;
    }
    case 15:
        value = (long)geteuid();
        break;
    case 16:
        value = socket(AF_UNIX, SOCK_STREAM | SOCK_CLOEXEC | SOCK_NONBLOCK, 0);
        break;
    case 17: {
        struct sockaddr_un address = {0};
        if (!host_fd(first) || !host_path(left) || lean_sarray_size(left) > sizeof(address.sun_path)) {
            errno = EINVAL; break;
        }
        address.sun_family = AF_UNIX;
        memcpy(address.sun_path, lean_sarray_cptr(left), lean_sarray_size(left));
        value = connect((int)first, (const struct sockaddr *)&address,
            (socklen_t)(offsetof(struct sockaddr_un, sun_path) + lean_sarray_size(left)));
        break;
    }
    case 18: {
        struct pollfd descriptors[8] = {{0}};
        size_t length = lean_sarray_size(left);
        const unsigned char *input = lean_sarray_cptr(left);
        if (length % 16 || length > 16 * 8 || first > 100) { errno = EINVAL; break; }
        size_t number = length / 16;
        int valid = 1;
        for (size_t i = 0; i < number; i++) {
            uint64_t fd = 0, events = 0;
            for (size_t j = 0; j < 8; j++) fd |= (uint64_t)input[16*i+j] << (8*j);
            for (size_t j = 0; j < 8; j++) events |= (uint64_t)input[16*i+8+j] << (8*j);
            if (!host_fd(fd) || (events != POLLIN && events != POLLOUT)) { valid = 0; break; }
            descriptors[i].fd = (int)fd; descriptors[i].events = (short)events;
        }
        if (!valid) { errno = EINVAL; break; }
        value = poll(descriptors, (nfds_t)number, (int)first);
        if (value >= 0) {
            for (size_t i = 0; i < number; i++) host_word(buffer+8*i, (uint16_t)descriptors[i].revents);
            count = 8 * number;
        }
        break;
    }
    case 19: {
        int error = 0;
        socklen_t size = sizeof(error);
        if (!host_fd(first)) { errno = EBADF; break; }
        value = getsockopt((int)first, SOL_SOCKET, SO_ERROR, &error, &size);
        if (value == 0 && size == sizeof(error)) { host_word(buffer, (uint32_t)error); count = 8; }
        break;
    }
    case 20:
        if (!host_fd(first) || !host_path(left) || lean_sarray_size(right) > sizeof(buffer)) { errno = EINVAL; break; }
        value = fsetxattr((int)first, (const char *)lean_sarray_cptr(left), lean_sarray_cptr(right),
            lean_sarray_size(right), XATTR_CREATE);
        break;
    case 21:
        if (!host_fd(first) || !host_path(left) || second < 1 || second > sizeof(buffer)) { errno = EINVAL; break; }
        value = fgetxattr((int)first, (const char *)lean_sarray_cptr(left), buffer, (size_t)second);
        if (value >= 0 && (uint64_t)value <= second) count = (size_t)value;
        break;
    case 22:
        if (getcwd((char *)buffer, 4096)) { count = strlen((char *)buffer); value = 0; }
        break;
    case 23:
        if (first < 1 || first > INT_MAX || (second != SIGTERM && second != SIGKILL) || third > 1) {
            errno = EINVAL; break;
        }
        value = kill(third ? -(pid_t)first : (pid_t)first, (int)second);
        break;
    case 24: {
        unsigned int size = 0;
        if (lean_sarray_size(right) != 32) { errno = EINVAL; break; }
        if (HMAC(EVP_sha256(), lean_sarray_cptr(right), 32, lean_sarray_cptr(left),
                lean_sarray_size(left), buffer, &size) && size == 32) { value = 0; count = 32; }
        else errno = EIO;
        break;
    }
    case 25:
        if (lean_sarray_size(left) != lean_sarray_size(right) ||
            lean_sarray_size(left) > sizeof(buffer)) { errno = EINVAL; break; }
        value = CRYPTO_memcmp(lean_sarray_cptr(left), lean_sarray_cptr(right), lean_sarray_size(left)) == 0;
        break;
    case 26:
        if (!host_fd(first)) { errno = EBADF; break; }
        value = fcntl((int)first, F_SETFD, FD_CLOEXEC);
        break;
    case 27: {
        struct statx information = {0};
        if (!host_fd(first)) { errno = EBADF; break; }
        value = syscall(SYS_statx, (int)first, "", AT_EMPTY_PATH | AT_SYMLINK_NOFOLLOW,
            STATX_INO | STATX_MNT_ID, &information);
        if (value == 0) {
            if ((information.stx_mask & (STATX_INO | STATX_MNT_ID)) != (STATX_INO | STATX_MNT_ID)) {
                errno = EOPNOTSUPP; value = -1; break;
            }
            host_word(buffer, ((uint64_t)information.stx_dev_major << 32) | information.stx_dev_minor);
            host_word(buffer+8, information.stx_ino);
            host_word(buffer+16, information.stx_mnt_id);
            count = 24;
        }
        break;
    }
    case 28:
        value = syscall(SYS_openat, AT_FDCWD, "/proc/self/exe", O_RDONLY | O_CLOEXEC | O_NONBLOCK, 0);
        break;
    case 29: {
        struct statfs information = {0};
        if (!host_fd(first)) { errno = EBADF; break; }
        value = syscall(SYS_fstatfs, (int)first, &information);
        if (value == 0) {
            host_word(buffer, (uint64_t)(unsigned long)information.f_type);
            count = 8;
        }
        break;
    }
    case 30: {
        // §AR-host-boundary.primitives: GETFLAGS writes an int, not the encoded ioctl long.
        int flags = 0;
        if (!host_fd(first)) { errno = EBADF; break; }
        value = syscall(SYS_ioctl, (int)first, FS_IOC_GETFLAGS, &flags);
        if (value == 0) {
            for (size_t i = 0; i < 4; i++) buffer[i] = (unsigned char)((uint32_t)flags >> (8*i));
            count = 4;
        }
        break;
    }
    default:
        errno = ENOSYS;
        break;
    }
    int error = errno;
    return host_reply(value, error, buffer, count);
}

/* §AR-host-boundary.primitives: Borrow the descriptor of the rooted runtime handle. */
LEAN_EXPORT lean_obj_res leancage_host_handle_descriptor(b_lean_obj_arg handle) {
    FILE *stream = (FILE *)lean_get_external_data(handle);
    errno = 0;
    int descriptor = fileno(stream);
    int error = errno;
    return host_reply(descriptor, error, NULL, 0);
}
