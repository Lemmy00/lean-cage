// SPDX-License-Identifier: Apache-2.0
// §FS-lifecycle.evidence: Static hostile/allowed fixtures; execute only inside the M2 VM.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <linux/capability.h>
#include <sched.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/prctl.h>
#include <sys/stat.h>
#include <sys/fsuid.h>
#include <sys/syscall.h>
#include <sys/types.h>
#include <sys/sysmacros.h>
#include <sys/wait.h>
#include <unistd.h>
#include <grp.h>
extern char **environ;
static long raw(long nr) { long r; __asm__ volatile("syscall":"=a"(r):"a"(nr):"rcx","r11","memory"); return r; }
static int check(void) {
    uid_t r,e,s; gid_t gr,ge,gs;
    struct __user_cap_header_struct h={_LINUX_CAPABILITY_VERSION_3,0};
    struct __user_cap_data_struct caps[2]={{0},{0}};
    sigset_t mask; struct sigaction action; char cwd[8];
    if(getresuid(&r,&e,&s)||getresgid(&gr,&ge,&gs)||r!=65534||e!=65534||s!=65534||
       gr!=65534||ge!=65534||gs!=65534||getgroups(0,NULL)!=0||syscall(SYS_capget,&h,caps))return 1;
    if(setfsuid((uid_t)-1)!=65534 || setfsgid((gid_t)-1)!=65534)return 11;
    for(int i=0;i<2;i++)if(caps[i].effective||caps[i].permitted||caps[i].inheritable)return 2;
    for(int cap=0;cap<64;cap++) {
        int b=prctl(PR_CAPBSET_READ,cap,0,0,0);
        if(b<0&&errno==EINVAL)break;
        if(b!=0||prctl(PR_CAP_AMBIENT,PR_CAP_AMBIENT_IS_SET,cap,0,0)!=0)return 3;
    }
    if(prctl(PR_GET_NO_NEW_PRIVS,0,0,0,0)!=1||prctl(PR_GET_SECCOMP,0,0,0,0)!=2||
       raw(SYS_getpid)<=1||raw(SYS_getppid)!=-EPERM)return 4;
    struct stat input,output;
    if(fstat(0,&input)||!S_ISCHR(input.st_mode)||major(input.st_rdev)!=1||minor(input.st_rdev)!=3||
       fstat(1,&output)||!S_ISCHR(output.st_mode)||major(output.st_rdev)!=5||minor(output.st_rdev)!=1||umask(077)!=077)return 10;
    for(int fd=3;fd<1024;fd++)if(fcntl(fd,F_GETFD)>=0||errno!=EBADF)return 5;
    if(sigprocmask(SIG_SETMASK,NULL,&mask)||sigaction(SIGUSR1,NULL,&action)||
       action.sa_handler!=SIG_DFL)return 6;
    for(int sig=1;sig<=64;sig++)if(sigismember(&mask,sig)==1)return 7;
    if(!getcwd(cwd,sizeof(cwd))||strcmp(cwd,"/")||!environ[0]||strcmp(environ[0],"LC_ALL=C")||environ[1])return 8;
    if(setuid(0)==0||setgid(0)==0||setgroups(0,NULL)==0||unshare(CLONE_NEWNS)==0||
       unshare(CLONE_NEWUSER)==0||kill(1,SIGKILL)==0)return 9;
    printf("M2_GUEST check=ok uid=65534 nnp=1 filter=2 handles=closed signals=reset\n");
    fflush(stdout); return 0;
}
int main(int argc,char **argv) {
    if(argc!=2)return 80;
    int error=check(); if(error) { printf("M2_GUEST check=failed code=%d\n",error); return 80+error; }
    if(!strcmp(argv[1],"x32")) { raw(0x40000027);return 101; }
    if(!strcmp(argv[1],"i386")) { long result; __asm__ volatile("int $0x80":"=a"(result):"a"(20L):"memory");return 102; }
    if(!strcmp(argv[1],"exit125"))return 125;
    if(!strcmp(argv[1],"signal")) { raise(SIGTERM); return 90; }
    if(!strcmp(argv[1],"stop")) { raise(SIGSTOP); for(;;)pause(); }
    if(!strcmp(argv[1],"spin"))for(;;)pause();
    if(!strcmp(argv[1],"reexec")) {
        char *const args[]={"guest","descendant",NULL};char *const env[]={"LC_ALL=C",NULL};
        execve("/guest",args,env);return 100;
    }
    if(!strcmp(argv[1],"forkexec")) {
        pid_t child=fork(); if(child<0)return 91;
        if(!child) { char *const args[]={"guest","descendant",NULL}; char *const env[]={"LC_ALL=C",NULL};
            execve("/guest",args,env); _exit(92); }
        int status; if(waitpid(child,&status,0)!=child||!WIFEXITED(status)||WEXITSTATUS(status))return 93;
        puts("M2_DESCENDANT fork_exec=ok"); return 0;
    }
    if(!strcmp(argv[1],"daemon")) {
        int pipefd[2]; if(pipe(pipefd))return 94;
        pid_t child=fork(); if(child<0)return 95;
        if(!child) {
            close(pipefd[0]); if(setsid()<0)_exit(96);
            pid_t grandchild=fork(); if(grandchild<0)_exit(97); if(grandchild)_exit(0);
            puts("M2_DESCENDANT daemon=ready"); fflush(stdout);
            if(write(pipefd[1],"R",1)!=1)_exit(98);
            close(pipefd[1]); for(;;)pause();
        }
        close(pipefd[1]); char ready;
        ssize_t n=read(pipefd[0],&ready,1); close(pipefd[0]);
        return n==1&&ready=='R'?0:99;
    }
    return 0;
}
