// SPDX-License-Identifier: Apache-2.0
// §AR-host-boundary.primitives: Filesystem feature changes run only as this disposable VM's PID 1.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <linux/fs.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/io.h>
#include <sys/ioctl.h>
#include <sys/mount.h>
#include <sys/reboot.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/utsname.h>
#include <sys/wait.h>
#include <sys/xattr.h>
#include <unistd.h>

static void fail(const char *message) {
    printf("LOOKUP_VM_FAILURE %s errno=%d\n", message, errno);
    fflush(stdout);
    if (ioperm(0xf4, 1, 1) == 0) outb(0x11, 0xf4);
    reboot(RB_POWER_OFF);
    for (;;) pause();
}

static void directory(const char *path) {
    if (mkdir(path, 0755) && errno != EEXIST) fail("mkdir fixture");
}

static void copy_file(const char *source, const char *target) {
    int input = open(source, O_RDONLY | O_CLOEXEC);
    int output = open(target, O_WRONLY | O_CREAT | O_EXCL | O_CLOEXEC, 0555);
    if (input < 0 || output < 0) fail("copy fixture open");
    unsigned char bytes[65536];
    ssize_t count;
    while ((count = read(input, bytes, sizeof(bytes))) > 0) {
        size_t offset = 0;
        while (offset < (size_t)count) {
            ssize_t written = write(output, bytes + offset, (size_t)count - offset);
            if (written <= 0) fail("copy fixture write");
            offset += (size_t)written;
        }
    }
    if (count < 0 || close(input) || close(output)) fail("copy fixture close");
}

static void copy_inventory(void) {
    FILE *inventory = fopen("/inventory", "r");
    if (!inventory) fail("fixture inventory");
    char source[4096], target[4096];
    while (fgets(source, sizeof(source), inventory)) {
        source[strcspn(source, "\n")] = 0;
        int length = snprintf(target, sizeof(target), "/newroot%s", source);
        if (source[0] != '/' || length < 0 || (size_t)length >= sizeof(target)) fail("fixture inventory path");
        for (char *part = target + strlen("/newroot/"); *part; part++) {
            if (*part == '/') { *part = 0; directory(target); *part = '/'; }
        }
        copy_file(source, target);
    }
    if (ferror(inventory) || fclose(inventory)) fail("fixture inventory read");
}

static void run_case(const char *mode, const char *path) {
    fflush(stdout);
    pid_t child = fork();
    if (child < 0) fail("fork fixture");
    if (child == 0) {
        char *const arguments[] = { "/filesystem-access-check", (char *)mode, (char *)path, NULL };
        char *const environment[] = { "LC_ALL=C", "LEAN_NUM_THREADS=0", "LEAN_STACK_SIZE_KB=8192", NULL };
        execve(arguments[0], arguments, environment);
        _exit(127);
    }
    int status;
    pid_t waited;
    do { waited = waitpid(child, &status, 0); } while (waited < 0 && errno == EINTR);
    if (waited != child || !WIFEXITED(status) || WEXITSTATUS(status) != 0) fail("guard fixture execution");
    printf("LOOKUP_CASE mode=%s path=%s exit=0\n", mode, path);
}

int main(void) {
    if (getpid() != 1 || access("/leancage-host-lookup-vm", R_OK)) return 99;
    setvbuf(stdout, NULL, _IOLBF, 0);
    struct utsname kernel;
    if (uname(&kernel)) fail("uname");
    printf("LOOKUP_VM_PROFILE release=%s machine=%s uid=%lu\n", kernel.release, kernel.machine,
        (unsigned long)getuid());
    directory("/dev"); directory("/newroot");
    if (mount("devtmpfs", "/dev", "devtmpfs", 0, NULL)) fail("VM devtmpfs");
    if (mount("tmpfs", "/newroot", "tmpfs", 0, "mode=0755,size=512m")) fail("VM root tmpfs");
    copy_inventory();
    directory("/newroot/case"); directory("/newroot/plain"); directory("/newroot/proc"); directory("/newroot/dev");
    if (mount("devtmpfs", "/newroot/dev", "devtmpfs", 0, NULL)) fail("VM chroot devtmpfs");
    if (mount("/dev/vda", "/newroot/case", "ext4", MS_NOSUID | MS_NODEV, NULL)) fail("VM ext4");
    if (mount("proc", "/newroot/proc", "proc", MS_NOSUID | MS_NODEV | MS_NOEXEC, NULL)) fail("VM procfs");
    if (chroot("/newroot") || chdir("/")) fail("VM chroot");
    directory("/case/plain"); directory("/case/folded");
    int folded = open("/case/folded", O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    int flags = 0;
    if (folded < 0 || ioctl(folded, FS_IOC_GETFLAGS, &flags)) fail("VM GETFLAGS");
    flags |= FS_CASEFOLD_FL;
    if (ioctl(folded, FS_IOC_SETFLAGS, &flags)) fail("VM enable casefold");
    if (mkdirat(folded, ".leancage-private-alias", 0700)) fail("VM create private-name stage");
    int stage = openat(folded, ".leancage-private-alias", O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    int secret = stage < 0 ? -1 : openat(stage, "secret", O_WRONLY | O_CREAT | O_EXCL | O_CLOEXEC, 0600);
    if (secret < 0 || write(secret, "private-stage-fixture", 21) != 21 || close(secret)) fail("VM stage fixture");
    int alias = openat(folded, ".LEANCAGE-PRIVATE-alias", O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    struct stat original, alternate;
    if (alias < 0 || fstat(stage, &original) || fstat(alias, &alternate) ||
        original.st_dev != alternate.st_dev || original.st_ino != alternate.st_ino) fail("VM actual uppercase alias");
    unsigned char private_attribute;
    errno = 0;
    if (fgetxattr(stage, "user.leancage.private", &private_attribute, 1) >= 0 || errno != ENODATA)
        fail("VM stage should be unmarked");
    printf("LOOKUP_ALIAS actual_same_object=1 casefold=1 reserved_lowercase_stage=1\n");
    close(alias); close(stage); close(folded);
    run_case("useful", "/plain");
    run_case("useful", "/case/plain");
    run_case("casefold", "/case/folded");
    run_case("unsupported", "/proc");
    if (access("/case/folded/.leancage-private-alias/secret", R_OK) ||
        !access("/case/folded/visible", F_OK)) fail("VM denied rename modified names");
    printf("LOOKUP_VM_COMPLETE cases=4 failures=0\n");
    fflush(stdout);
    if (ioperm(0xf4, 1, 1) == 0) outb(0x10, 0xf4);
    reboot(RB_POWER_OFF);
    for (;;) pause();
}
