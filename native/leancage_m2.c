// SPDX-License-Identifier: Apache-2.0
// §AR-lifecycle.design: Original VM-only fixed-plan helper; C/Linux refinement remains M4.
#define _GNU_SOURCE
#include <elf.h>
#include <errno.h>
#include <fcntl.h>
#include <grp.h>
#include <limits.h>
#include <linux/capability.h>
#include <linux/filter.h>
#include <linux/memfd.h>
#include <linux/seccomp.h>
#include <linux/securebits.h>
#include <poll.h>
#include <sched.h>
#include <signal.h>
#include <stdint.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mount.h>
#include <sys/prctl.h>
#include <sys/ptrace.h>
#include <sys/signalfd.h>
#include <sys/stat.h>
#include <sys/fsuid.h>
#include <sys/syscall.h>
#include <sys/sysmacros.h>
#include <sys/types.h>
#include <sys/utsname.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

#if !defined(__x86_64__)
#error "M2 supports Linux x86-64 only"
#endif
_Static_assert(sizeof(uid_t)==4 && sizeof(gid_t)==4, "Linux credential ID ABI");
_Static_assert(sizeof(long) == 8 && sizeof(void *) == 8 && sizeof(int) == 4, "LP64 ABI");
_Static_assert(sizeof(struct sock_filter) == 8 && sizeof(struct sock_fprog) == 16, "BPF ABI");
_Static_assert(offsetof(struct sock_filter,code)==0 && offsetof(struct sock_filter,jt)==2 &&
               offsetof(struct sock_filter,jf)==3 && offsetof(struct sock_filter,k)==4 &&
               offsetof(struct sock_fprog,len)==0 && offsetof(struct sock_fprog,filter)==8,
               "BPF field offsets");

static const struct sock_filter canonical[9] = {
    {0x20,0,0,4}, {0x15,1,0,0xc000003e}, {6,0,0,0x80000000},
    {0x20,0,0,0}, {0x35,0,1,0x40000000}, {6,0,0,0x80000000},
    {0x15,0,1,110}, {6,0,0,0x50001}, {6,0,0,0x7fff0000}
};
// §FS-lifecycle.supervision: Fixed-width trusted frames never share writers with guest code.
struct frame { uint32_t magic, kind, phase, detail, entry, clean; };
_Static_assert(sizeof(struct frame) == 24, "M2 frame ABI");
enum { MAGIC = 0x3247434c, EXITED = 0, SETUP = 1, SIGNALLED = 2, CANCELLED = 3, UNKNOWN = 4, READY = 5 };
static const char *mode;
static int ismode(const char *name) { return strcmp(mode, name) == 0; }
static int err(void) { return errno > 0 && errno <= 4095 ? errno : EIO; }

// §FS-lifecycle.supervision: Loop short reports/EINTR; failure cannot fall through to exec.
static int write_all(int fd, const void *data, size_t size, size_t chunk) {
    const unsigned char *p = data;
    while (size) {
        size_t count = size < chunk ? size : chunk;
        ssize_t n = write(fd, p, count);
        if (n < 0 && errno == EINTR) continue;
        if (n <= 0) return -1;
        p += n; size -= (size_t)n;
    }
    return 0;
}
static _Noreturn void fail_child(int fd, unsigned phase, int error) {
    struct frame f = {MAGIC, SETUP, phase, (unsigned)error, 0, 0};
    if (ismode("report_drop")) close(fd);
    else if (ismode("report_short")) (void)write_all(fd, &f, 7, 7);
    else (void)write_all(fd, &f, sizeof(f), ismode("short_io") ? 1 : sizeof(f));
    _exit(125);
}
static struct frame outcome(unsigned kind, unsigned phase, unsigned detail, unsigned entry) {
    return (struct frame){MAGIC, kind, phase, detail, entry, 0};
}

// §FS-lifecycle.profile: Guard before namespace, filter, credential or hostile test operations.
static int profile(void) {
    struct utsname u;
    if (uname(&u) || strcmp(u.release,"6.18.59") || strcmp(u.machine,"x86_64")) return ENOTSUP;
    int fd = open("/leancage-m2-disposable-vm", O_RDONLY|O_CLOEXEC|O_NOFOLLOW);
    char marker[32] = {0};
    if (fd < 0) return ENOTSUP;
    ssize_t n = read(fd, marker, sizeof(marker)); close(fd);
    if (n != (ssize_t)(sizeof("LeanCage-M2-root-VM-v1")-1) ||
        memcmp(marker, "LeanCage-M2-root-VM-v1", sizeof("LeanCage-M2-root-VM-v1")-1)) return ENOTSUP;
    if (getuid() || geteuid() || getgid() || getegid()) return EPERM;
    int stdin_flags=fcntl(0,F_GETFD);
    if(stdin_flags<0) {
        if(errno!=EBADF)return err();
        if(open("/dev/null",O_RDONLY|O_CLOEXEC)!=0)return ENOTSUP;
    }
    FILE *status = fopen("/proc/self/status", "r");
    if (!status) return err();
    // An inherited filter can fake PR_GET_SECCOMP=0 with SECCOMP_RET_ERRNO|0.
    // A fresh procfs open must return a positive non-stdio descriptor; require all fields.
    char line[256]; unsigned tracer=UINT32_MAX, filters=UINT32_MAX, process=0;
    if(fileno(status)<=2) { fclose(status); return ENOTSUP; }
    while (fgets(line,sizeof(line),status)) {
        unsigned value;
        if(sscanf(line,"TracerPid: %u",&value)==1)tracer=value;
        if(sscanf(line,"Seccomp: %u",&value)==1)filters=value;
        if(sscanf(line,"Pid: %u",&value)==1)process=value;
    }
    fclose(status);
    pid_t self=getpid();
    return self>0 && process==(unsigned)self && tracer==0 && filters==0 ? 0 : ENOTSUP;

}

// §FS-lifecycle.resources: Check the snapshot, not a path later looked up by exec.
static int elf_ok(int fd, off_t size) {
    Elf64_Ehdr h;
    if (size < (off_t)sizeof(h) || pread(fd,&h,sizeof(h),0) != (ssize_t)sizeof(h)) return ENOEXEC;
    if (memcmp(h.e_ident,ELFMAG,SELFMAG) || h.e_ident[EI_CLASS]!=ELFCLASS64 ||
        h.e_ident[EI_DATA]!=ELFDATA2LSB || h.e_ident[EI_VERSION]!=EV_CURRENT ||
        h.e_machine!=EM_X86_64 || h.e_type!=ET_EXEC || h.e_version!=EV_CURRENT ||
        h.e_ehsize!=sizeof(h) || h.e_phentsize!=sizeof(Elf64_Phdr) ||
        !h.e_phnum || h.e_phnum>128) return ENOEXEC;
    uint64_t bytes=(uint64_t)h.e_phnum*sizeof(Elf64_Phdr), total=(uint64_t)size;
    if (h.e_phoff>total || bytes>total-h.e_phoff) return ENOEXEC;
    int entry=0;
    for (unsigned i=0;i<h.e_phnum;i++) {
        Elf64_Phdr p;
        if (pread(fd,&p,sizeof(p),(off_t)(h.e_phoff+(uint64_t)i*sizeof(p)))!=(ssize_t)sizeof(p)) return ENOEXEC;
        if (p.p_type==PT_INTERP) return ENOEXEC;
        if (p.p_type!=PT_LOAD) continue;
        if (p.p_filesz>p.p_memsz || p.p_offset>total || p.p_filesz>total-p.p_offset ||
            p.p_memsz>UINT64_MAX-p.p_vaddr) return ENOEXEC;
        if ((p.p_flags&PF_X) && h.e_entry>=p.p_vaddr && h.e_entry-p.p_vaddr<p.p_memsz) entry=1;
    }
    return entry ? 0 : ENOEXEC;
}
static int snapshot(const char *path) {
    int source=open(path,O_RDONLY|O_NOFOLLOW|O_CLOEXEC);
    if (source<0) return -1;
    struct stat s;
    int dest=-1, error=0;
    if (fstat(source,&s)) error=err();
    else if (!S_ISREG(s.st_mode) || s.st_size<=0 || s.st_size>16*1024*1024) error=EFBIG;
    else if (!(s.st_mode&0111)) error=EACCES;
    else {
        dest=(int)syscall(SYS_memfd_create,"leancage-m2-image",MFD_CLOEXEC|MFD_ALLOW_SEALING);
        if (dest<0) error=err();
    }
    if (!error) {
        unsigned char buffer[4096]; off_t offset=0;
        while (offset<s.st_size) {
            size_t want=(size_t)(s.st_size-offset); if(want>sizeof(buffer)) want=sizeof(buffer);
            ssize_t n=pread(source,buffer,want,offset);
            if(n<=0) { error=n<0?err():EIO; break; }
            if(write_all(dest,buffer,(size_t)n,sizeof(buffer))) { error=err(); break; }
            offset+=n;
        }
        if(!error) error=elf_ok(dest,s.st_size);
        if(!error && fchmod(dest,0555)) error=err();
        int seals=F_SEAL_WRITE|F_SEAL_GROW|F_SEAL_SHRINK|F_SEAL_SEAL;
        if(!error && fcntl(dest,F_ADD_SEALS,seals)) error=err();
        if(!error && fcntl(dest,F_GET_SEALS)!=seals) error=EPROTO;
    }
    if(close(source) && !error) error=err();
    if(error) { if(dest>=0)close(dest); errno=error; return -1; }
    int high=fcntl(dest,F_DUPFD_CLOEXEC,20); error=err(); close(dest); errno=error;
    return high;
}

// §FS-lifecycle.resources: Reset even glibc-reserved signal dispositions using the x86-64 ABI.
static int reset_signals(void) {
    uint64_t mask=UINT64_MAX;
    if(syscall(SYS_rt_sigprocmask,SIG_SETMASK,&mask,NULL,8)) return err();
    struct { uintptr_t handler,flags,restorer; uint64_t mask; } action={0};
    for(int sig=1;sig<=64;sig++) {
        if(sig==SIGKILL || sig==SIGSTOP) continue;
        if(syscall(SYS_rt_sigaction,sig,&action,NULL,8)) return err();
    }
    mask=0;
    return syscall(SYS_rt_sigprocmask,SIG_SETMASK,&mask,NULL,8) ? err() : 0;
}
static int parent_alive(int fd) {
    struct pollfd p={fd,POLLIN,0};
    int r=poll(&p,1,0);
    return r==0 ? 0 : r<0 ? err() : ECHILD;
}

// §FS-lifecycle.setup: Drop all credential forms, not just no-new-privileges.
static int credentials(void) {
    if(prctl(PR_SET_SECUREBITS,SECBIT_NOROOT|SECBIT_NOROOT_LOCKED|
             SECBIT_NO_SETUID_FIXUP|SECBIT_NO_SETUID_FIXUP_LOCKED,0,0,0)) return err();
    for(unsigned cap=0;cap<64;cap++) {
        int present=prctl(PR_CAPBSET_READ,cap,0,0,0);
        if(present<0 && errno==EINVAL) break;
        if(present<0 || prctl(PR_CAPBSET_DROP,cap,0,0,0)) return err();
    }
    if(prctl(PR_CAP_AMBIENT,PR_CAP_AMBIENT_CLEAR_ALL,0,0,0) || setgroups(0,NULL) ||
       setresgid(65534,65534,65534) || setresuid(65534,65534,65534)) return err();
    struct __user_cap_header_struct h={_LINUX_CAPABILITY_VERSION_3,0};
    struct __user_cap_data_struct caps[2]={{0},{0}};
    if(ismode("credentials_fail")) h.version=0;
    if(syscall(SYS_capset,&h,caps)) return err();
    if(syscall(SYS_capget,&h,caps)) return err();
    for(int i=0;i<2;i++) if(caps[i].effective||caps[i].permitted||caps[i].inheritable) return EPROTO;
    uid_t r,e,s; gid_t gr,ge,gs;
    if(getresuid(&r,&e,&s)||getresgid(&gr,&ge,&gs)||getgroups(0,NULL)!=0 ||
       r!=65534||e!=65534||s!=65534||gr!=65534||ge!=65534||gs!=65534) return EPROTO;
    if(setfsuid((uid_t)-1)!=65534 || setfsgid((gid_t)-1)!=65534)return EPROTO;
    return prctl(PR_SET_DUMPABLE,0,0,0,0) ? err() : 0;
}

// §AR-lifecycle.effects: Native fixed-plan dispatcher; no allocation/runtime callbacks after fork.
static _Noreturn void guest(int executable, int report, int nullfd, const char *argument) {
    int error=reset_signals();
    if(error)fail_child(report,1,error);
    if(ptrace(PTRACE_TRACEME,0,NULL,NULL) || raise(SIGSTOP)) fail_child(report,1,err());
    if(dup3(executable,3,O_CLOEXEC)<0 || dup3(report,4,O_CLOEXEC)<0 ||
       dup2(nullfd,0)<0) fail_child(report,3,err());
    if(ismode("handles_fail")) { errno=0; if(dup3(-1,5,O_CLOEXEC)<0)fail_child(4,3,err()); }
    if(syscall(SYS_close_range,5u,UINT32_MAX,0u)) fail_child(4,3,err());
    if(chdir("/")) fail_child(4,3,err());
    umask(077);
    error=credentials(); if(error)fail_child(4,4,error);
    if(prctl(PR_GET_SECCOMP,0,0,0,0)!=0)fail_child(4,5,ENOTSUP);
    if(ismode("signal_setup")) { raise(SIGTERM); _exit(125); }
    if(ismode("cancel_before")) for(;;)pause();
    struct sock_filter instructions[9];
    memcpy(instructions,canonical,sizeof(instructions));
    struct sock_fprog program={9,instructions};
    char *const argv[]={"guest",(char *)argument,NULL};
    char *const env[]={"LC_ALL=C",NULL};
    int execfd=ismode("exec_fail")?-1:3;
    if(prctl(PR_SET_NO_NEW_PRIVS,ismode("nnp_fail")||ismode("short_io")?2:1,0,0,0))fail_child(4,6,err());
    if(ismode("filter_fail")||ismode("report_drop")||ismode("report_short"))program.len=0;
    if(prctl(PR_SET_SECCOMP,SECCOMP_MODE_FILTER,&program,0,0))fail_child(4,7,err());
    // §FS-lifecycle.setup: No optional call between successful install and the handle exec attempt.
    syscall(SYS_execveat,execfd,"",argv,env,AT_EMPTY_PATH);
    fail_child(4,8,err());
}

// §FS-lifecycle.supervision: Read a complete error frame plus EOF; absence is not exec evidence.
static size_t read_frame(int fd, struct frame *f) {
    size_t n=0;
    while(n<sizeof(*f)) {
        ssize_t r=read(fd,(char *)f+n,sizeof(*f)-n);
        if(r<0&&errno==EINTR)continue;
        if(r<0)return SIZE_MAX;
        if(!r)break;
        n+=(size_t)r;
    }
    if(n==sizeof(*f)) { char extra; ssize_t r; do { r=read(fd,&extra,1); }while(r<0&&errno==EINTR);
        if(r!=0)return SIZE_MAX; }
    return n;
}
static _Noreturn void namespace_init(int parentfd, int resultfd, int executable,
                                     int nullfd, const char *argument) {
    struct frame result=outcome(SETUP,2,0,0);
    int error=reset_signals();
    if(!error && prctl(PR_SET_PDEATHSIG,SIGKILL,0,0,0))error=err();
    if(!error)error=parent_alive(parentfd);
    if(!error && prctl(PR_SET_DUMPABLE,0,0,0,0))error=err();
    if(!error && (mount(NULL,"/",NULL,MS_REC|MS_PRIVATE,NULL) ||
       mount("proc","/proc",ismode("mount_fail")?"invalid-leancage":"proc",
             MS_NOSUID|MS_NODEV|MS_NOEXEC,NULL)))error=err();
    int pipefd[2]={-1,-1};
    if(!error && pipe2(pipefd,O_CLOEXEC))error=err();
    if(error) { result.detail=(unsigned)error; goto report; }
    // Keep error writer above the fixed 0..4 range even with sparse inherited descriptors.
    int writer=fcntl(pipefd[1],F_DUPFD_CLOEXEC,30);
    close(pipefd[1]);
    if(writer<0) { result.detail=(unsigned)err(); close(pipefd[0]); goto report; }
    uint64_t mask=UINT64_MAX;
    if(syscall(SYS_rt_sigprocmask,SIG_SETMASK,&mask,NULL,8)) {
        result.detail=(unsigned)err(); close(writer); close(pipefd[0]); goto report;
    }
    pid_t child=fork();
    if(child==0)guest(executable,writer,nullfd,argument);
    close(writer); close(executable); close(nullfd); close(parentfd);
    if(child<0) { result.detail=(unsigned)err(); close(pipefd[0]); goto report; }
    int status=0, entered=0, leader_done=0, supervision_error=0;
    pid_t waited;
    do { waited=waitpid(child,&status,0); }while(waited<0&&errno==EINTR);
    if(waited!=child || !WIFSTOPPED(status) || WSTOPSIG(status)!=SIGSTOP ||
       ptrace(PTRACE_SETOPTIONS,child,0,PTRACE_O_TRACEEXEC|PTRACE_O_EXITKILL) ||
       ptrace(PTRACE_CONT,child,0,0))supervision_error=1;
    while(!supervision_error && !leader_done) {
        do { waited=waitpid(-1,&status,__WALL); }while(waited<0&&errno==EINTR);
        if(waited<0) { supervision_error=1; break; }
        if(waited!=child)continue;
        if(WIFEXITED(status)||WIFSIGNALED(status)) { leader_done=1; break; }
        if(WIFSTOPPED(status)) {
            unsigned event=(unsigned)status>>16;
            if(event==PTRACE_EVENT_EXEC && !entered) {
                entered=1;
                struct frame ready=outcome(READY,8,0,1);
                if(write_all(resultfd,&ready,sizeof(ready),sizeof(ready))) { supervision_error=1; break; }
                if(ismode("init_death"))_exit(90);
            }
            int sig=event==PTRACE_EVENT_EXEC?0:WSTOPSIG(status);
            if(ptrace(PTRACE_CONT,child,0,sig))supervision_error=1;
        } else supervision_error=1;
    }
    int leader_status=status;
    // §FS-lifecycle.cancellation: PID-namespace kill cannot target the VM sentinel/host processes.
    if(kill(-1,SIGKILL)<0 && errno!=ESRCH)supervision_error=1;
    for(;;) {
        waited=waitpid(-1,&status,__WALL);
        if(waited>0)continue;
        if(waited<0&&errno==EINTR)continue;
        if(waited<0&&errno==ECHILD)break;
        supervision_error=1; break;
    }
    struct frame failure={0}; size_t received=read_frame(pipefd[0],&failure); close(pipefd[0]);
    if(!supervision_error && !entered && received==sizeof(failure) && failure.magic==MAGIC &&
       failure.kind==SETUP && failure.phase>=1 && failure.phase<=8 &&
       failure.detail>0 && failure.detail<=4095 && failure.entry==0 && failure.clean==0) result=failure;
    else if(!supervision_error && entered && received==0 && leader_done && WIFEXITED(leader_status))
        result=outcome(EXITED,0,(unsigned)WEXITSTATUS(leader_status),1);
    else if(!supervision_error && entered && received==0 && leader_done && WIFSIGNALED(leader_status))
        result=outcome(SIGNALLED,0,(unsigned)WTERMSIG(leader_status),1);
    else result=outcome(UNKNOWN,9,EPROTO,entered?1:2);
report:
    result.clean=1;
    if(ismode("final_drop")) { close(resultfd); _exit(0); }
    if(ismode("final_short")) (void)write_all(resultfd,&result,7,7);
    else (void)write_all(resultfd,&result,sizeof(result),ismode("short_io")?1:sizeof(result));
    close(resultfd); _exit(0);
}

static uint64_t milliseconds(void) {
    struct timespec t;
    if(clock_gettime(CLOCK_MONOTONIC,&t))return 0;
    return (uint64_t)t.tv_sec*1000+(uint64_t)t.tv_nsec/1000000;
}
static int finish(struct frame result) {
    printf("M2_RESULT kind=%u phase=%u detail=%u entry=%u clean=%u\n",
           result.kind,result.phase,result.detail,result.entry,result.clean);
    fflush(stdout);
    if(result.kind==EXITED)return (int)result.detail;
    if(result.kind==SIGNALLED)return 128+(int)result.detail;
    return result.kind==SETUP?125:result.kind==CANCELLED?124:126;
}

// §FS-lifecycle.profile: Fresh static helper is the only native process boundary.
int main(int argc,char **argv) {
    mode=argc==6?argv[3]:"invalid";
    int error=profile();
    if(error)return finish(outcome(SETUP,1,(unsigned)error,0));
    if(argc!=6 || strcmp(argv[1],"12345678") || strlen(argv[2])>4095 || argv[2][0]!='/' ||
       strlen(argv[4])>64)return finish(outcome(SETUP,1,EINVAL,0));
    const char *modes[]={"normal","namespace_fail","mount_fail","handles_fail","credentials_fail",
        "nnp_fail","filter_fail","exec_fail","report_drop","report_short","short_io",
        "final_drop","final_short","signal_setup","cancel_before","cancel","parent_death",
        "controller_death","init_death","existing_filter","snapshot_rename","deadline","early_helper_death","early_controller_death"};
    int known=0;
    for(unsigned i=0;i<sizeof(modes)/sizeof(modes[0]);i++)if(ismode(modes[i]))known=1;
    if(!known)return finish(outcome(SETUP,1,EINVAL,0));
    error=reset_signals(); if(error)return finish(outcome(SETUP,1,(unsigned)error,0));
    if(ismode("existing_filter")) {
        struct sock_filter allow={6,0,0,SECCOMP_RET_ALLOW}; struct sock_fprog p={1,&allow};
        if(prctl(PR_SET_NO_NEW_PRIVS,1,0,0,0)||prctl(PR_SET_SECCOMP,SECCOMP_MODE_FILTER,&p,0,0))
            return finish(outcome(SETUP,1,(unsigned)err(),0));
    }
    if(prctl(PR_GET_SECCOMP,0,0,0,0)!=0)return finish(outcome(SETUP,1,ENOTSUP,0));
    struct stat out,errout;
    if(fstat(1,&out)||fstat(2,&errout)||!S_ISCHR(out.st_mode)||!S_ISCHR(errout.st_mode)||
       major(out.st_rdev)!=5||minor(out.st_rdev)!=1||major(errout.st_rdev)!=5||minor(errout.st_rdev)!=1)
        return finish(outcome(SETUP,1,ENOTSUP,0));
    // §FS-lifecycle.cancellation: Use the controller identity supplied before spawn.
    char *parent_end=NULL; errno=0;
    unsigned long expected_parent=strtoul(argv[5],&parent_end,10);
    if(errno || !*argv[5] || *parent_end || !expected_parent || expected_parent>INT_MAX)
        return finish(outcome(SETUP,1,EINVAL,0));
    pid_t original_parent=(pid_t)expected_parent;
    if(getppid()!=original_parent)return finish(outcome(SETUP,1,ECHILD,0));
    int parentfd=(int)syscall(SYS_pidfd_open,original_parent,0);
    if(parentfd<0)return finish(outcome(SETUP,1,(unsigned)err(),0));
    if(getppid()!=original_parent) { close(parentfd); return finish(outcome(SETUP,1,ECHILD,0)); }
    if(ismode("early_controller_death")) {
        if(syscall(SYS_pidfd_send_signal,parentfd,SIGKILL,NULL,0))
            return finish(outcome(SETUP,1,(unsigned)err(),0));
        struct pollfd dead={parentfd,POLLIN,0}; int observed;
        do { observed=poll(&dead,1,-1); }while(observed<0 && errno==EINTR);
        if(observed!=1)return finish(outcome(UNKNOWN,1,EPROTO,2));
    }
    if(prctl(PR_SET_PDEATHSIG,SIGKILL,0,0,0)||parent_alive(parentfd)||getppid()!=original_parent)
        { close(parentfd); return finish(outcome(SETUP,1,ECHILD,0)); }
    int executable=snapshot(argv[2]);
    if(executable<0)return finish(outcome(SETUP,1,(unsigned)err(),0));
    if(ismode("snapshot_rename") && (rename(argv[2],"/snapshot-old")||
        rename("/replacement","/snapshot-guest"))) { close(executable); return finish(outcome(SETUP,1,(unsigned)err(),0)); }
    int opened_null=open("/dev/null",O_RDONLY|O_CLOEXEC);
    int nullfd=opened_null<0?-1:fcntl(opened_null,F_DUPFD_CLOEXEC,20);
    if(opened_null>=0)close(opened_null);
    int pipefd[2];
    if(nullfd<0 || pipe2(pipefd,O_CLOEXEC|O_NONBLOCK)) { close(executable); return finish(outcome(SETUP,1,(unsigned)err(),0)); }
    int selfpidfd=(int)syscall(SYS_pidfd_open,getpid(),0);
    sigset_t mask; sigemptyset(&mask); sigaddset(&mask,SIGTERM); sigaddset(&mask,SIGINT); sigaddset(&mask,SIGHUP);
    if(selfpidfd<0||sigprocmask(SIG_BLOCK,&mask,NULL))return finish(outcome(SETUP,1,(unsigned)err(),0));
    int signal_fd=signalfd(-1,&mask,SFD_CLOEXEC|SFD_NONBLOCK);
    if(signal_fd<0)return finish(outcome(SETUP,1,(unsigned)err(),0));
    unsigned long flags=CLONE_NEWPID|CLONE_NEWNS|CLONE_NEWIPC|CLONE_NEWNET|CLONE_NEWUTS|SIGCHLD;
    if(ismode("namespace_fail"))flags|=CLONE_THREAD;
    pid_t init=(pid_t)syscall(SYS_clone,flags,NULL,NULL,NULL,0);
    if(init==0) {
        close(pipefd[0]); close(signal_fd);
        // Control writer must be blocking; report frames are smaller than PIPE_BUF.
        if(fcntl(pipefd[1],F_SETFL,0))_exit(125);
        namespace_init(selfpidfd,pipefd[1],executable,nullfd,argv[4]);
    }
    if(init>0 && ismode("early_helper_death"))raise(SIGKILL);
    close(pipefd[1]); close(selfpidfd); close(executable); close(nullfd);
    if(init<0)return finish(outcome(SETUP,2,(unsigned)err(),0));
    int initfd=(int)syscall(SYS_pidfd_open,init,0);
    if(initfd<0) { kill(init,SIGKILL); waitpid(init,NULL,0); return finish(outcome(UNKNOWN,9,(unsigned)err(),2)); }
    printf("M2_SCOPE init=%d helper=%d\n",init,getpid()); fflush(stdout);
    struct frame result=outcome(UNKNOWN,9,EPROTO,2), incoming={0};
    size_t used=0; int got_final=0, entered=0, cancelled=0, protocol_bad=0;
    uint64_t start=milliseconds(), limit=ismode("cancel_before")||ismode("deadline")?250:10000;
    for(;;) {
        struct pollfd fds[3]={{initfd,POLLIN,0},{pipefd[0],POLLIN|POLLHUP,0},{signal_fd,POLLIN,0}};
        int r=poll(fds,3,10);
        if(r<0&&errno==EINTR)continue;
        if(r<0) { protocol_bad=1; break; }
        if(fds[1].revents&(POLLIN|POLLHUP)) {
            ssize_t n=read(pipefd[0],(char *)&incoming+used,sizeof(incoming)-used);
            if(n>0) {
                used+=(size_t)n;
                if(used==sizeof(incoming)) {
                    if(incoming.magic!=MAGIC)protocol_bad=1;
                    else if(incoming.kind==READY && incoming.phase==8 && incoming.entry==1 && !got_final && !entered) {
                        entered=1;
                        if(ismode("parent_death"))raise(SIGKILL);
                        if(ismode("controller_death")) (void)syscall(SYS_pidfd_send_signal,parentfd,SIGKILL,NULL,0);
                        if(ismode("cancel"))kill(getpid(),SIGTERM);
                    } else if(incoming.kind<=UNKNOWN && !got_final) { result=incoming; got_final=1; }
                    else protocol_bad=1;
                    used=0; memset(&incoming,0,sizeof(incoming));
                }
            } else if(n<0&&errno!=EAGAIN&&errno!=EINTR)protocol_bad=1;
        }
        if(fds[2].revents&POLLIN || milliseconds()-start>=limit) {
            struct signalfd_siginfo info; ssize_t signal_read=read(signal_fd,&info,sizeof(info));
            if(signal_read<0 && errno!=EAGAIN && errno!=EINTR)protocol_bad=1;
            if(syscall(SYS_pidfd_send_signal,initfd,SIGKILL,NULL,0)) { if(errno!=ESRCH)protocol_bad=1; }
            else cancelled=1;
        }
        if(fds[0].revents&POLLIN) {
            // Drain all buffered frames before interpreting namespace death.
            struct pollfd p={pipefd[0],POLLIN,0};
            if(poll(&p,1,0)>0 && p.revents&POLLIN)continue;
            break;
        }
    }
    if(protocol_bad) (void)syscall(SYS_pidfd_send_signal,initfd,SIGKILL,NULL,0);
    int status=0; pid_t waited;
    do { waited=waitpid(init,&status,0); }while(waited<0&&errno==EINTR);
    close(initfd); close(pipefd[0]); close(signal_fd); close(parentfd);
    if(waited!=init)return finish(outcome(UNKNOWN,9,ECHILD,entered?1:2));
    if(cancelled && WIFSIGNALED(status) && WTERMSIG(status)==SIGKILL)
        result=outcome(CANCELLED,0,0,entered?1:2);
    else if(!got_final||used||protocol_bad||!WIFEXITED(status)||WEXITSTATUS(status)!=0 ||
            result.clean!=1 || result.entry>2 || (result.kind==EXITED && (result.entry!=1||result.detail>255)) ||
            (result.kind==SETUP && (result.entry!=0||result.phase<1||result.phase>8||!result.detail||result.detail>4095)) ||
            (result.kind==SIGNALLED && (result.entry!=1||!result.detail||result.detail>64)))
        result=outcome(UNKNOWN,9,EPROTO,entered?1:2);
    result.clean=1;
    return finish(result);
}
