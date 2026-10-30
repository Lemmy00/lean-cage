// SPDX-License-Identifier: Apache-2.0
// §AR-m1-launch.binding: Original M1-only Linux binding; native correspondence is assumed.
#define _GNU_SOURCE
#include <lean/lean.h>
#include <elf.h>
#include <errno.h>
#include <fcntl.h>
#include <linux/filter.h>
#include <linux/seccomp.h>
#include <signal.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/prctl.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <sys/types.h>
#include <sys/utsname.h>
#include <sys/wait.h>
#include <unistd.h>

#if !defined(__x86_64__)
#error "The M1 native binding supports x86-64 only"
#endif

// §AR-filter-slice.bindings: Verify actual target widths, offsets, sizes and alignment.
_Static_assert(sizeof(void *) == 8 && sizeof(long) == 8 && sizeof(int) == 4, "LP64 only");
_Static_assert(sizeof(struct sock_filter) == 8 && _Alignof(struct sock_filter) == 4, "filter ABI");
_Static_assert(offsetof(struct sock_filter, code) == 0 && offsetof(struct sock_filter, jt) == 2 &&
               offsetof(struct sock_filter, jf) == 3 && offsetof(struct sock_filter, k) == 4, "fields");
_Static_assert(sizeof(struct sock_fprog) == 16 && _Alignof(struct sock_fprog) == 8 &&
               offsetof(struct sock_fprog, len) == 0 && offsetof(struct sock_fprog, filter) == 8,
               "fprog ABI");

enum { PREFLIGHT = 1, NO_NEW_PRIVS = 2, INSTALL = 3, EXEC = 4, WAIT = 5, PROTOCOL = 6 };
struct failure_message { uint32_t phase, error, receipts, kind; };

static uint64_t result(unsigned kind, unsigned phase, uint32_t detail, unsigned receipts) {
    return (uint64_t)kind | ((uint64_t)phase << 8) | ((uint64_t)detail << 16) |
           ((uint64_t)receipts << 48);
}

static int positive_errno(void) { return errno > 0 && errno <= 4095 ? errno : EIO; }

// §FS-filter-loading.installation.failure: Reporting can fail; the child still exits, never execs.
static _Noreturn void child_failure(int fd, unsigned phase, int error, unsigned receipts) {
    const struct failure_message message = { phase, (uint32_t)error, receipts,
                                             error == EINTR ? 4 : 1 };
    ssize_t ignored = write(fd, &message, sizeof(message));
    (void)ignored;
    _exit(125);
}

// §FS-filter-loading.installation.failure: Unexpected return conventions are contract violations.
static _Noreturn void child_call_failure(int fd, unsigned phase, int returned, unsigned receipts) {
    if (returned == -1 && errno > 0 && errno <= 4095)
        child_failure(fd, phase, errno, receipts);
    const struct failure_message message = { phase, EPROTO, receipts, 3 };
    ssize_t ignored = write(fd, &message, sizeof(message));
    (void)ignored;
    _exit(125);
}

// §FS-filter-loading.installation.binding: This is a guard against accidental host experiments.
static int vm_profile(void) {
    struct utsname name;
    if (uname(&name) < 0) return positive_errno();
    if (strcmp(name.machine, "x86_64") || strcmp(name.release, "6.18.59")) return ENOTSUP;
    int fd = open("/leancage-m1-disposable-vm", O_RDONLY | O_CLOEXEC);
    if (fd < 0) return ENOTSUP;
    const char expected[] = "LeanCage-M1-VM-v1";
    char marker[sizeof(expected)] = {0};
    ssize_t count = read(fd, marker, sizeof(expected) - 1);
    int closed = close(fd);
    if (count != (ssize_t)(sizeof(expected) - 1) ||
        memcmp(marker, expected, sizeof(expected) - 1) || closed) return ENOTSUP;
    return 0;
}

// §FS-filter-loading.installation.binding: Only static native ELF is supported, with bounded reads.
static int check_elf(const char *path) {
    int fd = open(path, O_RDONLY | O_CLOEXEC | O_NOFOLLOW);
    if (fd < 0) return positive_errno();
    int error = ENOEXEC;
    struct stat st;
    Elf64_Ehdr header;
    if (fstat(fd, &st) < 0) { error = positive_errno(); goto done; }
    if (!S_ISREG(st.st_mode) || st.st_size < (off_t)sizeof(header)) goto done;
    if (pread(fd, &header, sizeof(header), 0) != (ssize_t)sizeof(header)) goto done;
    if (memcmp(header.e_ident, ELFMAG, SELFMAG) || header.e_ident[EI_CLASS] != ELFCLASS64 ||
        header.e_ident[EI_DATA] != ELFDATA2LSB || header.e_machine != EM_X86_64 ||
        header.e_type != ET_EXEC || header.e_version != EV_CURRENT ||
        header.e_ehsize != sizeof(header) || header.e_phentsize != sizeof(Elf64_Phdr) ||
        header.e_phnum == 0 || header.e_phnum > 128) goto done;
    uint64_t size = (uint64_t)st.st_size;
    uint64_t phbytes = (uint64_t)header.e_phnum * sizeof(Elf64_Phdr);
    if (header.e_phoff > size || phbytes > size - header.e_phoff) goto done;
    int executable_entry = 0;
    for (unsigned i = 0; i < header.e_phnum; i++) {
        Elf64_Phdr ph;
        off_t offset = (off_t)(header.e_phoff + (uint64_t)i * sizeof(ph));
        if (pread(fd, &ph, sizeof(ph), offset) != (ssize_t)sizeof(ph)) goto done;
        if (ph.p_type == PT_INTERP) goto done;
        if (ph.p_type != PT_LOAD) continue;
        if (ph.p_filesz > ph.p_memsz || ph.p_offset > size || ph.p_filesz > size - ph.p_offset)
            goto done;
        if ((ph.p_flags & PF_X) && header.e_entry >= ph.p_vaddr &&
            header.e_entry - ph.p_vaddr < ph.p_memsz) executable_entry = 1;
    }
    if (executable_entry) error = 0;
done:
    if (close(fd) < 0 && error == 0) error = positive_errno();
    return error;
}

// §FS-filter-loading.input.layout: Copy individual fields; never cast byte storage into structs.
static void copy_filter(struct sock_filter out[9], const unsigned char *bytes) {
    for (unsigned i = 0; i < 9; i++) {
        const unsigned char *p = bytes + 8 * i;
        out[i].code = (uint16_t)((uint16_t)p[0] | ((uint16_t)p[1] << 8));
        out[i].jt = p[2];
        out[i].jf = p[3];
        out[i].k = (uint32_t)p[4] | ((uint32_t)p[5] << 8) |
                   ((uint32_t)p[6] << 16) | ((uint32_t)p[7] << 24);
    }
}

// §FS-filter-loading.installation.entry: Mask first, reset even NPTL-reserved handlers, unmask.
static int reset_signals(void) {
    uint64_t mask = UINT64_MAX;
    if (syscall(SYS_rt_sigprocmask, SIG_SETMASK, &mask, NULL, 8) < 0) return positive_errno();
    struct kernel_sigaction {
        uintptr_t handler, flags, restorer;
        uint64_t mask;
    } action = {0};
    for (int sig = 1; sig <= 64; sig++) {
        if (sig == SIGKILL || sig == SIGSTOP) continue;
        if (syscall(SYS_rt_sigaction, sig, &action, NULL, 8) < 0) return positive_errno();
    }
    mask = 0;
    if (syscall(SYS_rt_sigprocmask, SIG_SETMASK, &mask, NULL, 8) < 0) return positive_errno();
    return 0;
}

// §FS-filter-loading.installation.binding: All storage and handles are prepared before fork.
LEAN_EXPORT lean_obj_res leancage_m1_launch(b_lean_obj_arg bytes, b_lean_obj_arg path,
                                           uint32_t mode, lean_obj_arg world) {
    (void)world;
    uint64_t outcome;
    int error = vm_profile();
    const char *target = lean_string_cstr(path);
    size_t path_size = lean_string_size(path);
    if (!error && (mode > 5 || path_size == 0 || path_size > 4096 || target[0] != '/' ||
                   strlen(target) + 1 != path_size || lean_sarray_size(bytes) != 72)) error = EINVAL;
    if (!error) error = check_elf(target);
    if (error) {
        outcome = result(1, PREFLIGHT, (uint32_t)error, 0);
        return lean_io_result_mk_ok(lean_box_uint64(outcome));
    }
    char executable[4096];
    memcpy(executable, target, path_size);
    struct sock_filter instructions[9];
    copy_filter(instructions, lean_sarray_cptr(bytes));
    struct sock_fprog program = { .len = 9, .filter = instructions };
    char *argument = mode == 4 ? "x32" : mode == 5 ? "i386" : "check";
    char *const argv[] = { executable, argument, NULL };
    char *const environment[] = { "LC_ALL=C", NULL };
    int pipefd[2];
    if (pipe2(pipefd, O_CLOEXEC) < 0)
        return lean_io_result_mk_ok(lean_box_uint64(result(1, PREFLIGHT, positive_errno(), 0)));
    pid_t child = fork();
    if (child < 0) {
        error = positive_errno();
        close(pipefd[0]); close(pipefd[1]);
        return lean_io_result_mk_ok(lean_box_uint64(result(1, PREFLIGHT, error, 0)));
    }
    if (child == 0) {
        if (close(pipefd[0]) < 0) child_failure(pipefd[1], PREFLIGHT, positive_errno(), 0);
        error = reset_signals();
        if (error) child_failure(pipefd[1], PREFLIGHT, error, 0);
        if (prctl(PR_GET_SECCOMP, 0UL, 0UL, 0UL, 0UL) != 0)
            child_failure(pipefd[1], PREFLIGHT, ENOTSUP, 0);
        if (mode == 3) { kill(getpid(), SIGTERM); _exit(125); }
        int returned = prctl(PR_SET_NO_NEW_PRIVS, mode == 1 ? 2UL : 1UL, 0UL, 0UL, 0UL);
        if (returned != 0) child_call_failure(pipefd[1], NO_NEW_PRIVS, returned, 1);
        if (mode == 2) program.len = 0;
        returned = prctl(PR_SET_SECCOMP, SECCOMP_MODE_FILTER, &program, 0UL, 0UL);
        if (returned != 0) child_call_failure(pipefd[1], INSTALL, returned, 3);
        // §FS-filter-loading.installation.effects: No allocation or authored syscall before execve.
        returned = execve(executable, argv, environment);
        child_call_failure(pipefd[1], EXEC, returned, 15);
    }
    int close_error = close(pipefd[1]) < 0 ? positive_errno() : 0;
    struct failure_message message = {0};
    size_t received = 0;
    int read_error = 0;
    while (received < sizeof(message)) {
        ssize_t count = read(pipefd[0], (char *)&message + received, sizeof(message) - received);
        if (count < 0 && errno == EINTR) continue;
        if (count < 0) { read_error = positive_errno(); break; }
        if (count == 0) break;
        received += (size_t)count;
    }
    if (close(pipefd[0]) < 0 && !close_error) close_error = positive_errno();
    int status = 0;
    pid_t waited;
    do { waited = waitpid(child, &status, 0); } while (waited < 0 && errno == EINTR);
    if (waited != child) outcome = result(3, WAIT, positive_errno(), 0);
    else if (read_error || close_error) outcome = result(3, PROTOCOL, read_error ? read_error : close_error, 0);
    else if (received == sizeof(message) && message.phase >= PREFLIGHT && message.phase <= EXEC &&
             message.error > 0 && message.error <= 4095 &&
             (message.kind == 1 || message.kind == 3 || message.kind == 4))
        outcome = result(message.kind, message.phase, message.error, message.receipts);
    else if (received != 0) outcome = result(3, PROTOCOL, EIO, 0);
    else if (WIFSIGNALED(status)) outcome = result(2, 0, WTERMSIG(status), 0);
    else if (!WIFEXITED(status) || WEXITSTATUS(status) == 125) outcome = result(3, PROTOCOL, EIO, 0);
    else outcome = result(0, 0, WEXITSTATUS(status), 0);
    return lean_io_result_mk_ok(lean_box_uint64(outcome));
}
