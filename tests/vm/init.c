// SPDX-License-Identifier: Apache-2.0
// §AR-m1-launch.vm: PID 1 in the disposable VM; never run this executable on the host.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/io.h>
#include <sys/mount.h>
#include <sys/reboot.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/utsname.h>
#include <sys/wait.h>
#include <unistd.h>
#include <grp.h>

struct test_case { const char *name, *filter, *executable, *mode; int exit_code; };

static int run_case(const struct test_case *test) {
    printf("CASE_BEGIN name=%s\n", test->name);
    fflush(stdout);
    pid_t child = fork();
    if (child < 0) return 1;
    if (child == 0) {
        if (setgroups(0, NULL) || setgid(65534) || setuid(65534)) _exit(124);
        char *const argv[] = { "/leancage-m1", (char *)test->filter,
            (char *)test->executable, (char *)test->mode, NULL };
        char *const env[] = { "LC_ALL=C", "LEAN_NUM_THREADS=1", "LEAN_STACK_SIZE_KB=8192", NULL };
        execve(argv[0], argv, env);
        _exit(124);
    }
    int status;
    pid_t waited;
    do { waited = waitpid(child, &status, 0); } while (waited < 0 && errno == EINTR);
    int code = waited == child && WIFEXITED(status) ? WEXITSTATUS(status) : 255;
    printf("CASE_END name=%s exit=%d expected=%d\n", test->name, code, test->exit_code);
    fflush(stdout);
    return code != test->exit_code;
}

int main(void) {
    if (getpid() != 1) return 99;
    mkdir("/proc", 0555); mkdir("/sys", 0555); mkdir("/tmp", 01777);
    if (mount("proc", "/proc", "proc", MS_NOSUID | MS_NODEV | MS_NOEXEC, NULL) ||
        mount("sysfs", "/sys", "sysfs", MS_NOSUID | MS_NODEV | MS_NOEXEC, NULL)) return 98;
    struct utsname name;
    if (uname(&name) || strcmp(name.release, "6.18.59")) return 97;
    printf("VM_PROFILE kernel=%s machine=%s pid1_uid=%lu\n", name.release, name.machine,
           (unsigned long)getuid());
    FILE *cpu = fopen("/proc/cpuinfo", "r");
    if (cpu) {
        char line[512];
        while (fgets(line, sizeof(line), cpu)) {
            if (strstr(line, "model name") || strstr(line, "microcode") ||
                strstr(line, "cpu family") || strstr(line, "vendor_id"))
                printf("VM_CPU %s", line);
        }
        fclose(cpu);
    }
    const struct test_case tests[] = {
        {"allowed_and_denied", "/filter.bin", "/guest", "0", 0},
        {"empty", "/empty.bin", "/guest", "0", 64},
        {"truncated", "/truncated.bin", "/guest", "0", 64},
        {"permissive", "/permissive.bin", "/guest", "0", 64},
        {"oversized", "/oversized.bin", "/guest", "0", 64},
        {"byte_order", "/byte-order.bin", "/guest", "0", 64},
        {"bad_elf", "/filter.bin", "/bad-elf", "0", 125},
        {"nnp_failure", "/filter.bin", "/guest", "1", 125},
        {"install_failure", "/filter.bin", "/guest", "2", 125},
        {"exec_failure", "/filter.bin", "/guest-noexec", "0", 125},
        {"terminated_setup", "/filter.bin", "/guest", "3", 143},
        {"x32_rejected", "/filter.bin", "/guest", "4", 159},
        {"i386_rejected", "/filter.bin", "/guest", "5", 159},
    };
    int failures = 0;
    for (size_t i = 0; i < sizeof(tests) / sizeof(tests[0]); i++) failures += run_case(&tests[i]);
    printf("VM_COMPLETE cases=%zu failures=%d\n", sizeof(tests) / sizeof(tests[0]), failures);
    fflush(stdout);
    sync();
    if (ioperm(0xf4, 1, 1) == 0) outb(failures ? 0x11 : 0x10, 0xf4);
    reboot(RB_POWER_OFF);
    for (;;) pause();
}
