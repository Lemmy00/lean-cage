// SPDX-License-Identifier: Apache-2.0
// §AR-workspace-vm.lifetime: PID 1 owns the controller and the private control UART.
#define _GNU_SOURCE
#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <inttypes.h>
#include <poll.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/io.h>
#include <sys/mount.h>
#include <sys/reboot.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <sys/types.h>
#include <sys/utsname.h>
#include <sys/wait.h>
#include <termios.h>
#include <time.h>
#include <unistd.h>

static int channel = -1;
static uint64_t out_cap, err_cap, space_cap, inode_cap;
static unsigned fault;

static uint32_t get32(const unsigned char *p) {
    uint32_t n = 0;
    for (unsigned i = 0; i < 4; i++) n |= (uint32_t)p[i] << (8*i);
    return n;
}
static uint64_t get64(const unsigned char *p) {
    uint64_t n = 0;
    for (unsigned i = 0; i < 8; i++) n |= (uint64_t)p[i] << (8*i);
    return n;
}
static void put32(unsigned char *p, uint32_t n) {
    for (unsigned i = 0; i < 4; i++) p[i] = (unsigned char)(n >> (8*i));
}
static void put64(unsigned char *p, uint64_t n) {
    for (unsigned i = 0; i < 8; i++) p[i] = (unsigned char)(n >> (8*i));
}
static int write_all(int fd, const void *bytes, size_t size) {
    const unsigned char *p = bytes;
    while (size) {
        ssize_t n = write(fd, p, size);
        if (n < 0 && errno == EINTR) continue;
        if (n <= 0) return -1;
        p += n; size -= (size_t)n;
    }
    return 0;
}
static ssize_t read_file(const char *path, void *data, size_t cap) {
    int fd = open(path, O_RDONLY | O_CLOEXEC | O_NOFOLLOW | O_NONBLOCK);
    if (fd < 0) return -1;
    struct stat st;
    if (fstat(fd, &st) || !S_ISREG(st.st_mode) || st.st_size < 0 || (uint64_t)st.st_size > cap) {
        close(fd); return -1;
    }
    size_t used = 0;
    while (used < cap) {
        ssize_t n = read(fd, (char *)data + used, cap - used);
        if (n < 0 && errno == EINTR) continue;
        if (n < 0) { close(fd); return -1; }
        if (!n) break;
        used += (size_t)n;
    }
    close(fd);
    return used == (uint64_t)st.st_size ? (ssize_t)used : -1;
}
static int control(const char *path, const char *text) {
    int fd = open(path, O_WRONLY | O_CLOEXEC);
    if (fd < 0) return -1;
    int result = write_all(fd, text, strlen(text));
    if (close(fd)) result = -1;
    return result;
}
static uint64_t millis(void) {
    struct timespec t;
    if (clock_gettime(CLOCK_MONOTONIC, &t)) return 0;
    return (uint64_t)t.tv_sec * 1000 + (uint64_t)t.tv_nsec / 1000000;
}
static int header(unsigned tag, uint64_t size) {
    unsigned char bytes[16] = {0};
    put32(bytes, tag); put64(bytes+8, size);
    return write_all(channel, bytes, sizeof(bytes));
}
static int send_file(unsigned tag, const char *path, uint64_t cap, const char *sha) {
    int fd = open(path, O_RDONLY | O_CLOEXEC | O_NOFOLLOW | O_NONBLOCK);
    if (fd < 0) return -1;
    struct stat st;
    if (fstat(fd, &st) || !S_ISREG(st.st_mode) || st.st_size < 0 || (uint64_t)st.st_size > cap ||
        header(tag, (uint64_t)st.st_size + (sha ? 64 : 0)) || (sha && write_all(channel, sha, 64))) {
        close(fd); return -1;
    }
    char bytes[16384]; uint64_t left = (uint64_t)st.st_size;
    while (left) {
        size_t amount = left < sizeof(bytes) ? (size_t)left : sizeof(bytes);
        ssize_t n = read(fd, bytes, amount);
        if (n < 0 && errno == EINTR) continue;
        if (n <= 0 || write_all(channel, bytes, (size_t)n)) { close(fd); return -1; }
        left -= (uint64_t)n;
    }
    return close(fd);
}

// §AR-workspace-vm.lifetime: Only the controller's direct helper child can be cancelled.
static pid_t helper_child(pid_t controller) {
    char path[160], text[8192], executable[128];
    DIR *processes = opendir("/proc");
    if (!processes) return 0;
    pid_t found = 0;
    struct dirent *entry;
    unsigned inspected = 0;
    // The pinned kernel omits CONFIG_PROC_CHILDREN; PPid is available in status.
    // Bound enumeration even if a hostile guest continuously forks and exits.
    while (!found && inspected++ < 4096 && (entry = readdir(processes))) {
        char *end;
        long child = strtol(entry->d_name, &end, 10);
        if (child <= 1 || child > INT32_MAX || *end) continue;
        snprintf(path, sizeof(path), "/proc/%ld/status", child);
        int fd = open(path, O_RDONLY | O_CLOEXEC);
        ssize_t n = fd < 0 ? -1 : read(fd, text, sizeof(text)-1);
        if (fd >= 0) close(fd);
        if (n <= 0) continue;
        text[n] = 0;
        char *parent = strstr(text, "\nPPid:\t");
        long parent_pid = 0;
        if (!parent || sscanf(parent, "\nPPid:\t%ld", &parent_pid) != 1 || parent_pid != controller) continue;
        snprintf(path, sizeof(path), "/proc/%ld/exe", child);
        n = readlink(path, executable, sizeof(executable)-1);
        if (n <= 0) continue;
        executable[n] = 0;
        if (!strcmp(executable, "/leancage-m3-helper")) found = (pid_t)child;
    }
    closedir(processes);
    return found;
}

static int cancel_helper(pid_t controller) {
    char path[128], text[8192], expected[128];
    long pid = helper_child(controller);
    if (!pid) return 0;
    int pidfd = (int)syscall(SYS_pidfd_open, (pid_t)pid, 0);
    if (pidfd < 0) return 0;
    snprintf(path, sizeof(path), "/proc/%ld/exe", pid);
    ssize_t n = readlink(path, expected, sizeof(expected)-1);
    if (n <= 0) { close(pidfd); return 0; }
    expected[n] = 0;
    if (strcmp(expected, "/leancage-m3-helper")) { close(pidfd); return 0; }
    snprintf(path, sizeof(path), "/proc/%ld/status", pid);
    int fd = open(path, O_RDONLY | O_CLOEXEC);
    n = fd < 0 ? -1 : read(fd, text, sizeof(text)-1);
    if (fd >= 0) close(fd);
    if (n <= 0) { close(pidfd); return 0; }
    text[n] = 0;
    char *blocked = strstr(text, "\nSigBlk:\t");
    char *parent = strstr(text, "\nPPid:\t");
    long parent_pid = 0;
    unsigned long long mask = 0;
    int armed = parent && sscanf(parent, "\nPPid:\t%ld", &parent_pid) == 1 && parent_pid == controller &&
        blocked && sscanf(blocked, "\nSigBlk:\t%llx", &mask) == 1 &&
        (mask & (1ULL << (SIGTERM-1)));
    int result = armed && !syscall(SYS_pidfd_send_signal, pidfd, SIGTERM, NULL, 0);
    close(pidfd); return result;
}

static int command(const char *mode, const char *argument, const char *output, int cancellable) {
    int fd = open(output, O_WRONLY | O_CREAT | O_EXCL | O_CLOEXEC, 0600);
    if (fd < 0) return 126;
    pid_t child = fork();
    if (child < 0) { close(fd); return 126; }
    if (!child) {
        if (dup2(fd, STDOUT_FILENO) < 0) _exit(126);
        close(fd);
        char *const args[] = {"/leancage", (char *)mode, (char *)argument, NULL};
        char *const env[] = {"LC_ALL=C", NULL};
        execve(args[0], args, env); _exit(126);
    }
    close(fd);
    int pending = 0, delivered = 0, status;
    uint64_t began = millis();
    for (;;) {
        pid_t done = waitpid(child, &status, WNOHANG);
        if (done == child) break;
        if (done < 0 && errno != EINTR) return 126;
        struct pollfd p = {channel, POLLIN, 0};
        if (poll(&p, 1, 10) > 0) {
            unsigned char byte;
            if (p.revents & POLLIN) {
                ssize_t n = read(channel, &byte, 1);
                if (n != 1 || byte != 'C') pending = 1;
                else pending = 1;
            }
            if (p.revents & (POLLHUP | POLLERR | POLLNVAL)) pending = 1;
        }
        if (pending && cancellable && !delivered) delivered = cancel_helper(child);
        // Faults are trusted acceptance inputs, never guest-controlled environment variables.
        if (fault == 1 && cancellable) (void)mkdir("/m3-results/1/report.json", 0700);
        if (millis() - began > 3630000) { kill(child, SIGKILL); waitpid(child, &status, 0); return 126; }
    }
    return WIFEXITED(status) ? WEXITSTATUS(status) : WIFSIGNALED(status) ? 128+WTERMSIG(status) : 126;
}

static int profile(void) {
    struct utsname uts;
    if (getuid() || uname(&uts) || strcmp(uts.release, "6.18.59")) return -1;
    if (mount("proc", "/proc", "proc", MS_NOSUID|MS_NODEV|MS_NOEXEC, NULL) ||
        mount("sysfs", "/sys", "sysfs", MS_NOSUID|MS_NODEV|MS_NOEXEC, NULL) ||
        mount("cgroup2", "/sys/fs/cgroup", "cgroup2", 0, NULL) ||
        control("/sys/fs/cgroup/cgroup.subtree_control", "+memory +pids +cpu") ||
        mkdir("/sys/fs/cgroup/m3", 0755) ||
        control("/sys/fs/cgroup/m3/cgroup.subtree_control", "+memory +pids +cpu") ||
        mount("/m3-runtime", "/m3-runtime", NULL, MS_BIND, NULL) ||
        mount(NULL, "/m3-runtime", NULL, MS_BIND|MS_REMOUNT|MS_RDONLY|MS_NOSUID|MS_NODEV, NULL)) return -1;
    return 0;
}
static int digest_name(const char *s) {
    if (strlen(s) != 64) return 0;
    for (unsigned i = 0; i < 64; i++) if (!((s[i] >= '0' && s[i] <= '9') || (s[i] >= 'a' && s[i] <= 'f'))) return 0;
    return 1;
}
static int exports(const char *root) {
    char path[256];
    snprintf(path, sizeof(path), "%s/export.manifest", root);
    if (access(path, F_OK)) return errno == ENOENT ? 0 : -1;
    if (send_file(5, path, 16*1024*1024, NULL)) return -1;
    snprintf(path, sizeof(path), "%s/blobs", root);
    DIR *dir = opendir(path);
    if (!dir) return -1;
    uint64_t total = 0, count = 0; int error = 0;
    for (;;) {
        errno = 0; struct dirent *entry = readdir(dir);
        if (!entry) { if (errno) error = -1; break; }
        if (!strcmp(entry->d_name, ".") || !strcmp(entry->d_name, "..")) continue;
        if (!digest_name(entry->d_name) || ++count > inode_cap) { error = -1; break; }
        struct stat st;
        if (fstatat(dirfd(dir), entry->d_name, &st, AT_SYMLINK_NOFOLLOW) || !S_ISREG(st.st_mode) ||
            st.st_size < 0 || (uint64_t)st.st_size > space_cap-total) { error = -1; break; }
        total += (uint64_t)st.st_size;
        snprintf(path, sizeof(path), "%s/blobs/%s", root, entry->d_name);
        if (send_file(6, path, space_cap, entry->d_name)) { error = -1; break; }
    }
    closedir(dir); return error;
}
static int scopes_extinct(void) {
    DIR *d = opendir("/sys/fs/cgroup/m3");
    if (!d) return 0;
    int result = 1;
    for (;;) {
        errno = 0; struct dirent *e = readdir(d);
        if (!e) { if (errno) result = 0; break; }
        if (e->d_name[0] >= '0' && e->d_name[0] <= '9') { result = 0; break; }
    }
    closedir(d); return result;
}
static void poweroff(int success) {
    if (channel >= 0) { tcdrain(channel); close(channel); }
    sync();
    if (!ioperm(0xf4, 4, 1)) outl(success ? 0x10 : 0x11, 0xf4);
    reboot(RB_POWER_OFF);
    for (;;) pause();
}

int main(void) {
    unsigned char request[152];
    if (read_file("/request/config", request, sizeof(request)) != sizeof(request) ||
        memcmp(request, "LCREQ1\0\0", 8)) poweroff(0);
    unsigned mode = get32(request+104);
    out_cap = get64(request+108); err_cap = get64(request+116);
    space_cap = get64(request+124); inode_cap = get64(request+132); fault = get32(request+140);
    if ((mode != 1 && mode != 2) || out_cap > 16777216 || err_cap > 16777216 ||
        space_cap > 268435456 || inode_cap > 65536 || fault > 2 || get64(request+144)) poweroff(0);
    channel = open("/dev/ttyS1", O_RDWR | O_NOCTTY | O_CLOEXEC);
    struct termios settings;
    if (channel < 0 || tcgetattr(channel, &settings)) poweroff(0);
    cfmakeraw(&settings); settings.c_cflag |= CLOCAL|CREAD;
    if (tcsetattr(channel, TCSANOW, &settings) || write_all(channel, "LCVM1\0\0\0", 8) ||
        write_all(channel, request+8, 96) || profile()) poweroff(0);
    unsigned exit_code = (unsigned)command(mode == 1 ? "check" : "run", "/request/policy.json", "/controller.json", mode == 2);
    unsigned transport_error = send_file(1, "/controller.json", 65536, NULL) ? EIO : 0;
    if (fault == 2) poweroff(0);
    unsigned retrieved = 126;
    unsigned char counter[8];
    uint64_t run = read_file("/m3-runs/allocator", counter, 8) == 8 ? get64(counter) : 0;
    if (mode == 2 && run == 1) {
        retrieved = (unsigned)command("report", "1", "/retrieved.json", 0);
        if (!retrieved && send_file(2, "/retrieved.json", 65536, NULL)) transport_error = EIO;
        char path[128];
        for (unsigned i = 0; i < 2; i++) {
            snprintf(path, sizeof(path), "/m3-results/1/%s", i ? "stderr" : "stdout");
            if (!access(path, F_OK) && send_file(3+i, path, i ? err_cap : out_cap, NULL)) transport_error = EIO;
        }
        if (exports("/m3-results/1")) transport_error = EIO;
    }
    unsigned char terminal[16];
    put32(terminal, exit_code); put32(terminal+4, retrieved);
    put32(terminal+8, transport_error); put32(terminal+12, (unsigned)scopes_extinct());
    int success = !transport_error && !header(7, 16) && !write_all(channel, terminal, 16);
    poweroff(success);
}
