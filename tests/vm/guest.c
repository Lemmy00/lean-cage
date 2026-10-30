// SPDX-License-Identifier: Apache-2.0
// §FS-filter-loading.input.subset: Trusted native workload measures allowed and denied actions.
#define _GNU_SOURCE
#include <errno.h>
#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <sys/prctl.h>
#include <sys/types.h>
#include <unistd.h>

static long raw_syscall(long number) {
    long result;
    __asm__ volatile ("syscall" : "=a"(result) : "a"(number) : "rcx", "r11", "memory");
    return result;
}

int main(int argc, char **argv) {
    long pid = raw_syscall(39);
    long denied = raw_syscall(110);
    int nnp = prctl(PR_GET_NO_NEW_PRIVS, 0UL, 0UL, 0UL, 0UL);
    int seccomp = prctl(PR_GET_SECCOMP, 0UL, 0UL, 0UL, 0UL);
    printf("GUEST_RESULT getpid_positive=%d getppid_raw=%ld nnp=%d seccomp=%d uid=%lu\n",
           pid > 0, denied, nnp, seccomp, (unsigned long)getuid());
    fflush(stdout);
    if (pid <= 0 || denied != -EPERM || nnp != 1 || seccomp != 2 || getuid() != 65534)
        return 1;
    if (argc == 2 && strcmp(argv[1], "x32") == 0) {
        raw_syscall(0x40000027);
        return 2;
    }
    if (argc == 2 && strcmp(argv[1], "i386") == 0) {
        long result;
        __asm__ volatile ("int $0x80" : "=a"(result) : "a"(20) : "memory");
        (void)result;
        return 3;
    }
    return 0;
}
