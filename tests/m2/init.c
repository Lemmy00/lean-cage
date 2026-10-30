// SPDX-License-Identifier: Apache-2.0
// §AR-lifecycle.vm: Trusted PID 1, positive controls, owned cleanup checks; VM only.
#define _GNU_SOURCE
#include <errno.h>
#include <dirent.h>
#include <fcntl.h>
#include <grp.h>
#include <linux/filter.h>
#include <linux/seccomp.h>
#include <sched.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/io.h>
#include <sys/ipc.h>
#include <sys/mount.h>
#include <sys/prctl.h>
#include <sys/ptrace.h>
#include <sys/reboot.h>
#include <sys/shm.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <sys/types.h>
#include <sys/utsname.h>
#include <sys/wait.h>
#include <unistd.h>
struct test { const char *name,*filter,*target,*mode,*arg; int expected; };
static pid_t sentinel;
static int code(int status) { return WIFEXITED(status)?WEXITSTATUS(status):WIFSIGNALED(status)?128+WTERMSIG(status):255; }
static int controls(void) {
    int pair[2], ip, shared;
    if(socketpair(AF_UNIX,SOCK_STREAM,0,pair))return 1;
    close(pair[0]);close(pair[1]);
    ip=socket(AF_INET,SOCK_STREAM,0); if(ip<0)return 2;close(ip);
    shared=shmget(IPC_PRIVATE,4096,IPC_CREAT|0600); if(shared<0)return 3;
    if(shmctl(shared,IPC_RMID,NULL))return 4;
    mkdir("/sys/fs",0755);mkdir("/sys/fs/cgroup",0755);
    if(mount("cgroup2","/sys/fs/cgroup","cgroup2",0,NULL))return 5;
    FILE *f=fopen("/sys/fs/cgroup/cgroup.controllers","r");char line[512]={0};
    if(!f)return 6;
    if(!fgets(line,sizeof(line),f)) { fclose(f);return 7; }fclose(f);
    if(!strstr(line,"memory")||!strstr(line,"pids")||!strstr(line,"cpu"))return 8;
    pid_t child=(pid_t)syscall(SYS_clone,CLONE_NEWPID|CLONE_NEWNS|CLONE_NEWNET|CLONE_NEWIPC|CLONE_NEWUTS|SIGCHLD,NULL,NULL,NULL,0);
    if(child<0)return 9;
    if(!child)_exit(getpid()==1?0:1);
    int status;if(waitpid(child,&status,0)!=child||code(status))return 10;
    puts("M2_CONTROL namespaces=present unix=present inet=present sysvipc=present cgroup_cpu_memory_pids=present");
    return 0;
}
static int clean_children(void) {
    for(int i=0;i<200;i++) {
        int status;pid_t p;
        while((p=waitpid(-1,&status,WNOHANG))>0)if(p==sentinel)return 0;
        DIR *directory=opendir("/proc"); if(!directory)return 0;
        struct dirent *entry; int other=0;
        while((entry=readdir(directory))) {
            char *end; long pid=strtol(entry->d_name,&end,10);
            if(pid>0 && !*end && pid!=1 && pid!=sentinel) {
                char path[64],line[256];snprintf(path,sizeof(path),"/proc/%ld/status",pid);
                FILE *status=fopen(path,"r");if(!status)continue;
                while(fgets(line,sizeof(line),status)) { long parent;
                    if(sscanf(line,"PPid: %ld",&parent)==1) { if(parent==1)other++;break; }
                }
                fclose(status);
            }
        }
        closedir(directory);
        if(!other && kill(sentinel,0)==0)return 1;
        usleep(10000);
    }
    return 0;
}
static int run_case(const struct test *t) {
    printf("M2_CASE_BEGIN name=%s\n",t->name);fflush(stdout);
    if(!strcmp(t->name,"missing_profile") && rename("/leancage-m2-disposable-vm","/profile-held"))return 1;
    pid_t child=fork();if(child<0)return 1;
    if(!child) {
        if(!strcmp(t->name,"unprivileged_caller")) {
            if(setgroups(0,NULL)||setgid(65534)||setuid(65534))_exit(120);
        }
        if(!strcmp(t->name,"inherited_aliases")) {
            int fd=open("/sentinel-data",O_RDONLY);int dir=open("/",O_RDONLY|O_DIRECTORY);int pair[2];
            if(fd<0||dir<0||socketpair(AF_UNIX,SOCK_STREAM,0,pair)||dup2(fd,137)<0||dup2(dir,138)<0||dup2(pair[0],139)<0)_exit(120);
            close(0);
            signal(SIGUSR1,SIG_IGN);sigset_t mask;sigemptyset(&mask);sigaddset(&mask,SIGUSR1);sigprocmask(SIG_BLOCK,&mask,NULL);
        }
        if(!strcmp(t->name,"masked_filter")) {
            struct sock_filter instructions[]={{0x20,0,0,0},{0x15,0,1,SYS_prctl},
                {6,0,0,SECCOMP_RET_ERRNO},{6,0,0,SECCOMP_RET_ALLOW}};
            struct sock_fprog program={4,instructions};
            if(prctl(PR_SET_NO_NEW_PRIVS,1,0,0,0)||prctl(PR_SET_SECCOMP,SECCOMP_MODE_FILTER,&program,0,0)||
               prctl(PR_GET_SECCOMP,0,0,0,0)!=0)_exit(124);
            puts("M2_FILTER_CONTROL query_masked=1");fflush(stdout);
        }
        char *const env[]={"LC_ALL=C","LEAN_NUM_THREADS=1","LEAN_STACK_SIZE_KB=8192",NULL};
        if(!strcmp(t->name,"changed_plan")||!strcmp(t->name,"external_tracer")) {
            if(!strcmp(t->name,"external_tracer")) {
                if(ptrace(PTRACE_TRACEME,0,0,0)||raise(SIGSTOP))_exit(121);
            }
            char *const args[]={"/leancage-m2-helper",!strcmp(t->name,"changed_plan")?"12345687":"12345678","/guest","normal","check","1",NULL};
            execve(args[0],args,env);_exit(122);
        }
        char *const args[]={"/leancage-m2",(char *)t->filter,(char *)t->target,(char *)t->mode,(char *)t->arg,NULL};
        execve(args[0],args,env);_exit(123);
    }
    int status;pid_t p;
    do { p=waitpid(child,&status,0);
        if(p==child&&WIFSTOPPED(status)) {
            if(ptrace(PTRACE_CONT,child,0,0))return 1;
        } else break;
    }while(1);
    if(!strcmp(t->name,"missing_profile") && rename("/profile-held","/leancage-m2-disposable-vm"))return 1;
    int actual=p==child?code(status):255;
    int clean=clean_children();
    printf("M2_CASE_END name=%s exit=%d expected=%d owned_gone=%d sentinel_alive=%d\n",
        t->name,actual,t->expected,clean,kill(sentinel,0)==0);fflush(stdout);
    return actual!=t->expected||!clean;
}
int main(void) {
    if(getpid()!=1)return 99;
    if(mount("proc","/proc","proc",MS_NOSUID|MS_NODEV|MS_NOEXEC,NULL)||
       mount("sysfs","/sys","sysfs",MS_NOSUID|MS_NODEV|MS_NOEXEC,NULL))return 98;
    struct utsname u;if(uname(&u)||strcmp(u.release,"6.18.59"))return 97;
    printf("M2_PROFILE name=leancage-m2-linux-6.18.59-root-v1 kernel=%s uid=%d\n",u.release,getuid());
    FILE *cpu=fopen("/proc/cpuinfo","r");if(cpu) { char line[512];while(fgets(line,sizeof(line),cpu)) {
        if(strstr(line,"model name")||strstr(line,"microcode")||strstr(line,"vendor_id"))printf("M2_CPU %s",line);
    } fclose(cpu); }
    int control=controls();if(control) { printf("M2_CONTROL failed=%d errno=%d\n",control,errno);fflush(stdout);return 96; }
    sentinel=fork();if(sentinel<0)return 95;if(!sentinel)for(;;)pause();
    const struct test tests[]={
        {"allowed","/filter.bin","/guest","normal","check",0},
        {"inherited_aliases","/filter.bin","/guest","normal","check",0},
        {"exit125","/filter.bin","/guest","normal","exit125",125},
        {"fork_exec","/filter.bin","/guest","normal","forkexec",0},
        {"leader_reexec","/filter.bin","/guest","normal","reexec",0},
        {"daemon_escape","/filter.bin","/guest","normal","daemon",0},
        {"guest_signal","/filter.bin","/guest","normal","signal",143},
        {"x32_rejected","/filter.bin","/guest","normal","x32",159},
        {"i386_rejected","/filter.bin","/guest","normal","i386",159},
        {"empty","/empty.bin","/guest","normal","check",64},
        {"permissive","/permissive.bin","/guest","normal","check",64},
        {"missing_profile","/filter.bin","/guest","normal","check",125},
        {"unprivileged_caller","/filter.bin","/guest","normal","check",125},
        {"bad_elf","/filter.bin","/bad-elf","normal","check",125},
        {"symlink","/filter.bin","/guest-link","normal","check",125},
        {"noexec","/filter.bin","/guest-noexec","normal","check",125},
        {"existing_filter","/filter.bin","/guest","existing_filter","check",125},
        {"masked_filter","/filter.bin","/guest","normal","check",125},
        {"changed_plan","/filter.bin","/guest","normal","check",125},
        {"external_tracer","/filter.bin","/guest","normal","check",125},
        {"namespace_failure","/filter.bin","/guest","namespace_fail","check",125},
        {"mount_failure","/filter.bin","/guest","mount_fail","check",125},
        {"handles_failure","/filter.bin","/guest","handles_fail","check",125},
        {"credentials_failure","/filter.bin","/guest","credentials_fail","check",125},
        {"nnp_failure","/filter.bin","/guest","nnp_fail","check",125},
        {"filter_failure","/filter.bin","/guest","filter_fail","check",125},
        {"exec_failure","/filter.bin","/guest","exec_fail","check",125},
        {"short_io","/filter.bin","/guest","short_io","check",125},
        {"error_drop","/filter.bin","/guest","report_drop","check",126},
        {"error_short","/filter.bin","/guest","report_short","check",126},
        {"final_drop","/filter.bin","/guest","final_drop","check",126},
        {"final_short","/filter.bin","/guest","final_short","check",126},
        {"signal_setup","/filter.bin","/guest","signal_setup","check",126},
        {"cancel_before","/filter.bin","/guest","cancel_before","check",124},
        {"cancel_exec_race","/filter.bin","/guest","cancel","spin",124},
        {"deadline","/filter.bin","/guest","deadline","spin",124},
        {"stopped_guest","/filter.bin","/guest","deadline","stop",124},
        {"early_controller_death","/filter.bin","/guest","early_controller_death","check",137},
        {"early_helper_death","/filter.bin","/guest","early_helper_death","check",137},
        {"helper_death","/filter.bin","/guest","parent_death","spin",137},
        {"controller_death","/filter.bin","/guest","controller_death","spin",137},
        {"init_death","/filter.bin","/guest","init_death","spin",126},
        {"snapshot_rename","/filter.bin","/snapshot-guest","snapshot_rename","check",0}
    };
    int failures=0;
    for(unsigned i=0;i<sizeof(tests)/sizeof(tests[0]);i++)failures+=run_case(&tests[i]);
    printf("M2_COMPLETE cases=%zu failures=%d\n",sizeof(tests)/sizeof(tests[0]),failures);fflush(stdout);
    kill(sentinel,SIGKILL);waitpid(sentinel,NULL,0);sync();
    if(ioperm(0xf4,1,1)==0)outb(failures?0x11:0x10,0xf4);
    reboot(RB_POWER_OFF);for(;;)pause();
}
