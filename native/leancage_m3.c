// SPDX-License-Identifier: Apache-2.0
// §AR-workspace.filesystem: VM-only fresh helper; Linux/native correspondence remains an explicit
// obligation.
#define _GNU_SOURCE
#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <grp.h>
#include <inttypes.h>
#include <limits.h>
#include <linux/capability.h>
#include <linux/filter.h>
#include <linux/seccomp.h>
#include <linux/securebits.h>
#include <poll.h>
#include <sched.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/file.h>
#include <sys/fsuid.h>
#include <sys/mount.h>
#include <sys/prctl.h>
#include <sys/ptrace.h>
#include <sys/signalfd.h>
#include <sys/stat.h>
#include <sys/statvfs.h>
#include <sys/syscall.h>
#include <sys/sysmacros.h>
#include <sys/utsname.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>
#include "m3_filter.h"

#if !defined(__x86_64__)
#error "M3 supports Linux x86-64 only"
#endif
_Static_assert(sizeof(uid_t)==4 && sizeof(gid_t)==4 && sizeof(pid_t)==4, "32-bit Linux IDs");
_Static_assert(sizeof(int)==4 && sizeof(long)==8 && sizeof(void *)==8, "LP64 ABI");
_Static_assert(sizeof(struct sock_filter)==8 && sizeof(struct sock_fprog)==16, "BPF ABI");

enum { EXITED, SETUP, SIGNALLED, CANCELLED, UNKNOWN, ADMITTED, ENTERED, PREFLIGHT };
enum { REQUEST=1, DEADLINE=2, CPU=4, OUTPUT=8, ACCOUNTING=16, SETUP_TIMEOUT=32 };
struct result { uint32_t kind,stage,detail,entry,clean,triggers,uid; uint64_t run,cpu,peak,out,err,elapsed,oom,pids; uint32_t export_state,omitted,export_error; unsigned char export_digest[32]; };
struct policy { uint64_t memory,tasks,quota,cpu,wall,space,inodes,in,out,err; int export_files; char **args; };
static struct policy policy;
static uint64_t run_id;
static int workspace_mounted,preflight,identity_owned,guest_entered;
static const char *tree_digest,*stdin_digest;
static unsigned run_uid;
static char run_path[128],workspace[160],root_path[160],cgroup[160],result_path[160];
static const char *mode="normal";
static int fault(const char *name) { return strcmp(mode,name)==0; }
static int error_number(void) { return errno>0 && errno<=4095?errno:EIO; }
static uint64_t now_ms(void) { struct timespec t; if(clock_gettime(CLOCK_MONOTONIC,&t)||t.tv_sec<0||(uint64_t)t.tv_sec>UINT64_MAX/1000-1)return 0; return (uint64_t)t.tv_sec*1000+(uint64_t)t.tv_nsec/1000000; }
static int write_all(int fd,const void *data,size_t count) {
    const unsigned char *p=data;
    while(count) { ssize_t n=write(fd,p,count);if(n<0&&errno==EINTR)continue;if(n<=0)return -1;p+=n;count-=(size_t)n; }
    return 0;
}
static int write_text(const char *path,const char *text) {
    int fd=open(path,O_WRONLY|O_CLOEXEC|O_NOFOLLOW);if(fd<0)return -1;
    size_t length=strlen(text);ssize_t n;do{n=write(fd,text,length);}while(n<0&&errno==EINTR);
    int r=n==(ssize_t)length?0:-1;if(r&&n>=0)errno=EIO;int saved=errno;if(close(fd)&&!r)return -1;errno=saved;return r;
}
static int create_text(const char *path,const char *text,mode_t permissions) {
    int fd=open(path,O_WRONLY|O_CREAT|O_EXCL|O_CLOEXEC|O_NOFOLLOW,permissions);if(fd<0)return -1;
    int r=write_all(fd,text,strlen(text));int saved=errno;if(close(fd)&&!r)return -1;errno=saved;return r;
}
static int read_text(const char *path,char *buffer,size_t size) {
    int fd=open(path,O_RDONLY|O_CLOEXEC|O_NOFOLLOW);if(fd<0)return -1;
    size_t used=0;int result=0;
    while(used<size-1) { ssize_t n=read(fd,buffer+used,size-1-used);if(n<0&&errno==EINTR)continue;if(n<0){result=-1;break;}if(!n)break;used+=(size_t)n; }
    if(used==size-1) { char extra;ssize_t n=read(fd,&extra,1);if(n!=0){errno=EOVERFLOW;result=-1;} }
    buffer[used]=0;int saved=errno;close(fd);errno=saved;return result;
}
static int number(const char *text,uint64_t *value) {
    if(!*text)return -1;
    uint64_t result=0;
    for(const unsigned char *p=(const unsigned char *)text;*p;p++) {
        if(*p<'0'||*p>'9'||result>(UINT64_MAX-(*p-'0'))/10)return -1;
        result=result*10+(*p-'0');
    }
    *value=result;return 0;
}

// §AR-workspace.transport: Explicit little-endian framing; native struct padding never crosses the
// pipe.
static void put32(unsigned char *p,uint32_t x) { for(int i=0;i<4;i++)p[i]=(unsigned char)(x>>(8*i)); }
static void put64(unsigned char *p,uint64_t x) { for(int i=0;i<8;i++)p[i]=(unsigned char)(x>>(8*i)); }
static uint32_t get32(const unsigned char *p) { uint32_t x=0;for(int i=0;i<4;i++)x|=(uint32_t)p[i]<<(8*i);return x; }
static uint64_t get64(const unsigned char *p) { uint64_t x=0;for(int i=0;i<8;i++)x|=(uint64_t)p[i]<<(8*i);return x; }
enum { FRAME_SIZE=160 };
static int send_frame(int fd,uint64_t sequence,struct result result) {
    unsigned char bytes[FRAME_SIZE]={0};memcpy(bytes,"LC3R",4);bytes[4]=1;bytes[6]=(unsigned char)result.kind;
    put64(bytes+8,result.run);put64(bytes+16,sequence);put32(bytes+24,FRAME_SIZE-32);
    put32(bytes+32,result.stage);put32(bytes+36,result.detail);put32(bytes+40,result.entry);
    put32(bytes+44,result.clean);put32(bytes+48,result.triggers);put32(bytes+52,result.uid);
    put64(bytes+56,result.cpu);put64(bytes+64,result.peak);put64(bytes+72,result.out);
    put64(bytes+80,result.err);put64(bytes+88,result.elapsed);
    put32(bytes+96,result.export_state);put32(bytes+100,result.omitted);memcpy(bytes+104,result.export_digest,32);
    put64(bytes+136,result.oom);put64(bytes+144,result.pids);put32(bytes+152,result.export_error);
    if(fd!=1&&result.kind<=UNKNOWN&&fault("report_wrong_seq"))put64(bytes+16,sequence+1);
    if(fd!=1&&result.kind<=UNKNOWN&&fault("report_bad_reserved"))bytes[28]=1;
    if(fd!=1&&result.kind<=UNKNOWN&&fault("report_duplicate")){if(write_all(fd,bytes,sizeof(bytes)))return -1;}
    if(fd!=1&&result.kind<=UNKNOWN&&fault("report_short"))return write_all(fd,bytes,17);
    if(fd!=1&&result.kind<=UNKNOWN&&fault("report_drop"))return 0;
    return write_all(fd,bytes,sizeof(bytes));
}
static int decode_frame(const unsigned char *p,uint64_t sequence,struct result *r) {
    if(memcmp(p,"LC3R",4)||p[4]!=1||p[5]||p[7]||get64(p+8)!=run_id||
       get64(p+16)!=sequence||get32(p+24)!=FRAME_SIZE-32||get32(p+28))return -1;
    for(int i=156;i<FRAME_SIZE;i++)if(p[i])return -1;
    *r=(struct result){.kind=p[6],.stage=get32(p+32),.detail=get32(p+36),.entry=get32(p+40),
        .clean=get32(p+44),.triggers=get32(p+48),.uid=get32(p+52),.run=get64(p+8),
        .cpu=get64(p+56),.peak=get64(p+64),.out=get64(p+72),.err=get64(p+80),.elapsed=get64(p+88)};
    if(r->kind>PREFLIGHT||r->entry>2||r->clean>1||r->uid!=run_uid||r->triggers||r->cpu||r->peak||r->out||r->err)return -1;
    for(int i=96;i<156;i++)if(p[i])return -1;
    switch(r->kind){
    case EXITED: if(r->stage||r->detail>255||r->entry!=1) return -1;break;
    case SETUP: if(r->stage<1||r->stage>8||!r->detail||r->detail>4095||r->entry) return -1;break;
    case SIGNALLED: if(r->stage||!r->detail||r->detail>64||r->entry!=1)return -1;break;
    case UNKNOWN: if(r->stage!=9||!r->detail||r->detail>4095)return -1;break;
    case ADMITTED: if(r->stage||r->detail||r->entry||r->clean||!r->elapsed)return -1;break;
    case ENTERED: if(r->stage!=8||r->detail||r->entry!=1||r->clean)return -1;break;
    case PREFLIGHT: if(!preflight||r->stage||r->detail||r->entry)return -1;break;
    default:return -1;
    }
    return 0;
}
static struct result result_of(unsigned kind,unsigned stage,unsigned detail,unsigned entry) {
    return (struct result){.kind=kind,.stage=stage,.detail=detail,.entry=entry,.run=run_id,.uid=run_uid};
}
static _Noreturn void fail_child(int fd,unsigned stage,int error) {
    unsigned char bytes[8];put32(bytes,stage);put32(bytes+4,(uint32_t)error);
    if(!fault("error_drop")) (void)write_all(fd,bytes,fault("error_short")?3:8);
    _exit(125);
}
static int finish(struct result result) {
    (void)send_frame(1,0,result);
    if(result.kind==PREFLIGHT)return 0;
    if(result.kind==EXITED)return (int)result.detail;
    if(result.kind==SIGNALLED)return 128+(int)result.detail;
    return result.kind==SETUP?125:result.kind==CANCELLED?124:126;
}

// §FS-workspace.profile: Guard before performing namespace, credential, filter or workload
// operations.
static int check_profile(void) {
    struct utsname u;char marker[128],status[4096];
    if(uname(&u)||strcmp(u.release,"6.18.59")||strcmp(u.machine,"x86_64"))return ENOTSUP;
    if(read_text("/leancage-m3-disposable-vm",marker,sizeof(marker))||strcmp(marker,"LeanCage-M3-root-VM-v1"))return ENOTSUP;
    if(getuid()||geteuid()||getgid()||getegid())return EPERM;
    if(read_text("/proc/self/status",status,sizeof(status)))return error_number();
    char *tracer=strstr(status,"TracerPid:\t"),*filter=strstr(status,"Seccomp:\t");
    if(!tracer||!filter||strtoul(tracer+11,NULL,10)||strtoul(filter+9,NULL,10)||prctl(PR_GET_SECCOMP,0,0,0,0)!=0)return ENOTSUP;
    struct statvfs fs;if(statvfs("/m3-runtime",&fs)||!(fs.f_flag&ST_RDONLY))return ENOTSUP;
    if(read_text("/m3-runtime/.leancage-runtime",marker,sizeof(marker))||
        strcmp(marker,"sha256:70bda1e795ded2a684ef9815955e05829b14ee5bb5c3eb2a940648e88f10fce9"))return ENOTSUP;
    // §AR-workspace.resources: The pinned BLOCK=n kernel has no swap subsystem; require this
    // profile.
    if(access("/proc/swaps",F_OK)==0||errno!=ENOENT)return ENOTSUP;
    const char *owned[]={"/m3-runs","/m3-results","/m3-inputs","/m3-inputs/trees","/m3-inputs/blobs"};
    for(unsigned i=0;i<5;i++){struct stat s;if(lstat(owned[i],&s)||!S_ISDIR(s.st_mode)||s.st_uid||s.st_gid||(s.st_mode&0077))return ENOTSUP;}
    struct stat report;if(fstat(1,&report)||!S_ISFIFO(report.st_mode))return ENOTSUP;
    return 0;
}
static int reset_signals(void) {
    uint64_t mask=UINT64_MAX;
    if(syscall(SYS_rt_sigprocmask,SIG_SETMASK,&mask,NULL,8))return error_number();
    struct { uintptr_t handler,flags,restorer;uint64_t mask; } action={0};
    for(int signal=1;signal<=64;signal++)if(signal!=SIGKILL&&signal!=SIGSTOP&&
        syscall(SYS_rt_sigaction,signal,&action,NULL,8))return error_number();
    mask=0;return syscall(SYS_rt_sigprocmask,SIG_SETMASK,&mask,NULL,8)?error_number():0;
}
static int parent_alive(int fd) { struct pollfd p={fd,POLLIN,0};int n=poll(&p,1,0);return n==0?0:n<0?error_number():ECHILD; }
static int credentials(void) {
    if(prctl(PR_SET_SECUREBITS,SECBIT_NOROOT|SECBIT_NOROOT_LOCKED|SECBIT_NO_SETUID_FIXUP|SECBIT_NO_SETUID_FIXUP_LOCKED,0,0,0))return error_number();
    for(unsigned cap=0;cap<64;cap++) {
        int present=prctl(PR_CAPBSET_READ,cap,0,0,0);if(present<0&&errno==EINVAL)break;
        if(present<0||prctl(PR_CAPBSET_DROP,cap,0,0,0))return error_number();
    }
    if(prctl(PR_CAP_AMBIENT,PR_CAP_AMBIENT_CLEAR_ALL,0,0,0)||setgroups(0,NULL)||
       setresgid(run_uid,run_uid,run_uid)||setresuid(run_uid,run_uid,run_uid))return error_number();
    struct __user_cap_header_struct header={_LINUX_CAPABILITY_VERSION_3,0};
    struct __user_cap_data_struct caps[2]={{0},{0}};
    if(syscall(SYS_capset,&header,caps)||syscall(SYS_capget,&header,caps))return error_number();
    for(int i=0;i<2;i++)if(caps[i].effective||caps[i].permitted||caps[i].inheritable)return EPROTO;
    uid_t r,e,s;gid_t gr,ge,gs;
    if(getresuid(&r,&e,&s)||getresgid(&gr,&ge,&gs)||getgroups(0,NULL)||
       r!=run_uid||e!=run_uid||s!=run_uid||gr!=run_uid||ge!=run_uid||gs!=run_uid||
       (uid_t)setfsuid((uid_t)-1)!=run_uid||(gid_t)setfsgid((gid_t)-1)!=run_uid)return EPROTO;
    return prctl(PR_SET_DUMPABLE,0,0,0,0)?error_number():0;
}

// §FS-workspace.authority: A durable monotonic run identity and exclusive UID lease precede
// allocation.
static uint64_t reservation_bytes(void) { return policy.memory+policy.space*(policy.export_files?2:1)+policy.in+16777216; }
static int allocate_identity(void) {
    int lock=open("/m3-runs/allocator",O_RDWR|O_CREAT|O_CLOEXEC|O_NOFOLLOW,0600);
    if(lock<0)return -1;
    if(flock(lock,LOCK_EX)){close(lock);return -1;}
    uint64_t reserved=0;
    for(unsigned uid=100000;uid<=100999;uid++) {
        char path[128],text[64];struct stat st;snprintf(path,sizeof(path),"/m3-runs/%u",uid);
        if(lstat(path,&st)){if(errno==ENOENT)continue;close(lock);return -1;}
        if(!S_ISDIR(st.st_mode)||st.st_uid||st.st_gid||(st.st_mode&0077)){errno=EPROTO;close(lock);return -1;}
        snprintf(path,sizeof(path),"/m3-runs/%u/reservation",uid);uint64_t amount;
        if(read_text(path,text,sizeof(text))||number(text,&amount)||amount>1610612736ULL-reserved){errno=EPROTO;close(lock);return -1;}
        reserved+=amount;
    }
    if(reservation_bytes()>1610612736ULL-reserved){errno=EAGAIN;close(lock);return -1;}
    unsigned char bytes[8];ssize_t n=pread(lock,bytes,8,0);uint64_t previous=0;
    if(n==8)previous=get64(bytes);else if(n!=0){errno=EPROTO;close(lock);return -1;}
    if(previous==UINT64_MAX){errno=EOVERFLOW;close(lock);return -1;}
    run_id=previous+1;put64(bytes,run_id);
    if(pwrite(lock,bytes,8,0)!=8||fsync(lock)){close(lock);return -1;}
    for(run_uid=100000;run_uid<=100999;run_uid++) {
        snprintf(run_path,sizeof(run_path),"/m3-runs/%u",run_uid);
        if(!mkdir(run_path,0700))break;
        if(errno!=EEXIST){close(lock);return -1;}
    }
    if(run_uid>100999){errno=EAGAIN;close(lock);return -1;}
    identity_owned=1;
    snprintf(workspace,sizeof(workspace),"%s/workspace",run_path);
    snprintf(root_path,sizeof(root_path),"%s/root",run_path);
    snprintf(cgroup,sizeof(cgroup),"/sys/fs/cgroup/m3/%"PRIu64,run_id);
    snprintf(result_path,sizeof(result_path),"/m3-results/%"PRIu64,run_id);
    char path[256],text[64];snprintf(path,sizeof(path),"%s/reservation",run_path);snprintf(text,sizeof(text),"%"PRIu64,reservation_bytes());
    int result=create_text(path,text,0600);int saved=errno;close(lock);errno=saved;return result;
}

static int cg_write(const char *key,const char *value) { char path[256];snprintf(path,sizeof(path),"%s/%s",cgroup,key);return write_text(path,value); }
static int cg_number(const char *key,uint64_t value) { char text[64];snprintf(text,sizeof(text),"%"PRIu64,value);return cg_write(key,text); }
static int cg_read(const char *file,const char *key,uint64_t *value) {
    if(guest_entered&&fault("accounting_fail")&&!strcmp(file,"cpu.stat")){errno=EIO;return -1;}
    char path[256],text[4096];snprintf(path,sizeof(path),"%s/%s",cgroup,file);if(read_text(path,text,sizeof(text)))return -1;
    if(!key) { text[strcspn(text,"\n")]=0;return number(text,value); }
    char *line=text;
    while(line&&*line) { char *end=strchr(line,'\n');if(end)*end=0;
        size_t length=strlen(key);if(!strncmp(line,key,length)&&line[length]==' ')return number(line+length+1,value);
        line=end?end+1:NULL;
    }
    errno=EPROTO;return -1;
}
static int prepare_resources(void) {
    if(fault("cgroup_fail")){errno=EIO;return -1;}
    if(unshare(CLONE_NEWNS)||mount(NULL,"/",NULL,MS_REC|MS_PRIVATE,NULL))return -1;
    if(mkdir(workspace,0700)||mkdir(root_path,0700)||mkdir(result_path,0700)||mkdir(cgroup,0700))return -1;
    char options[128],quota[64];snprintf(options,sizeof(options),"size=%"PRIu64",nr_inodes=%"PRIu64",mode=0700",policy.space,policy.inodes);
    if(mount("tmpfs",workspace,"tmpfs",MS_NOSUID|MS_NODEV,options))return -1;
    workspace_mounted=1;if(chown(workspace,run_uid,run_uid))return -1;
    char path[256];snprintf(path,sizeof(path),"%s/.tmp",workspace);
    if(mkdir(path,0700)||chown(path,run_uid,run_uid))return -1;
    snprintf(quota,sizeof(quota),"%"PRIu64" 100000",policy.quota);
    if(cg_number("memory.max",policy.memory)||cg_number("memory.oom.group",1)||
       cg_number("pids.max",policy.tasks)||cg_write("cpu.max",quota)||cg_number("cpu.max.burst",0))return -1;
    uint64_t value;
    if(cg_read("memory.max",NULL,&value)||value!=policy.memory||cg_read("pids.max",NULL,&value)||value!=policy.tasks){errno=EPROTO;return -1;}
    if(cg_read("memory.oom.group",NULL,&value)||value!=1||cg_read("cpu.max.burst",NULL,&value)||value||
       cg_read("pids.current",NULL,&value)||value){errno=EPROTO;return -1;}
    char actual[128];snprintf(path,sizeof(path),"%s/cpu.max",cgroup);
    if(read_text(path,actual,sizeof(actual)))return -1;
    actual[strcspn(actual,"\n")]=0;if(strcmp(actual,quota)){errno=EPROTO;return -1;}
    return 0;
}

#include "m3_artifacts.h"

// §FS-workspace.results: Identity describes the exact normalized native plan, excluding transient
// parent PID.
static int record_identity(int argc,char **argv) {
    struct m3_sha hash;unsigned char bytes[32];char plan[65],filter[65],path[256],json[512];sha_init(&hash);
    for(int i=2;i<argc;i++)if(i!=12)sha_update(&hash,argv[i],strlen(argv[i])+1);
    sha_final(&hash,bytes);sha_hex(bytes,plan);sha_init(&hash);sha_update(&hash,m3_filter,sizeof(m3_filter));sha_final(&hash,bytes);sha_hex(bytes,filter);
    snprintf(json,sizeof(json),"{\"schema\":\"leancage-plan-identity-v1\",\"plan_sha256\":\"%s\",\"filter_sha256\":\"%s\"}",plan,filter);
    snprintf(path,sizeof(path),"%s/identity.json",result_path);return create_text(path,json,0400);
}

// §FS-workspace.filesystem: The child has a private root and no construction descriptor at guest
// entry.
static int bind_at(const char *source,const char *target,unsigned long flags) {
    return mount(source,target,NULL,MS_BIND,NULL)||mount(NULL,target,NULL,MS_BIND|MS_REMOUNT|flags,NULL)?-1:0;
}
static int construct_root(void) {
    char target[256],source[256],text[256];
    if(mount("/m3-runtime",root_path,NULL,MS_BIND,NULL))return -1;
    snprintf(target,sizeof(target),"%s/workspace",root_path);if(bind_at(workspace,target,MS_NOSUID|MS_NODEV))return -1;
    snprintf(target,sizeof(target),"%s/proc",root_path);
    if(mount("proc",target,fault("mount_fail")?"bad-fs":"proc",MS_NOSUID|MS_NODEV|MS_NOEXEC,"hidepid=2,subset=pid"))return -1;
    snprintf(target,sizeof(target),"%s/dev",root_path);if(mount("tmpfs",target,"tmpfs",MS_NOSUID|MS_NOEXEC,"size=65536,nr_inodes=32,mode=0755"))return -1;
    const char *devices[]={"null","zero","urandom"};unsigned minors[]={3,5,9};
    for(unsigned i=0;i<3;i++){snprintf(target,sizeof(target),"%s/dev/%s",root_path,devices[i]);if(mknod(target,S_IFCHR|0666,makedev(1,minors[i]))||chmod(target,0666))return -1;}
    const char *links[]={"fd","stdin","stdout","stderr"};const char *values[]={"/proc/self/fd","/proc/self/fd/0","/proc/self/fd/1","/proc/self/fd/2"};
    for(unsigned i=0;i<4;i++){snprintf(target,sizeof(target),"%s/dev/%s",root_path,links[i]);if(symlink(values[i],target))return -1;}
    const char *names[]={"passwd","group","hostname","hosts","resolv.conf"};
    for(unsigned i=0;i<5;i++) {
        snprintf(source,sizeof(source),"%s/%s",run_path,names[i]);snprintf(target,sizeof(target),"%s/etc/%s",root_path,names[i]);
        if(i==0)snprintf(text,sizeof(text),"root:x:0:0:root:/:/bin/sh\nguest:x:%u:%u:guest:/workspace:/bin/sh\n",run_uid,run_uid);
        else if(i==1)snprintf(text,sizeof(text),"root:x:0:\nguest:x:%u:\n",run_uid);
        else snprintf(text,sizeof(text),"%s",i==2?"sandbox\n":i==3?"127.0.0.1 localhost\n::1 localhost\n":"");
        if(create_text(source,text,0444)||bind_at(source,target,MS_RDONLY|MS_NOSUID|MS_NODEV|MS_NOEXEC))return -1;
    }
    if(mount(NULL,root_path,NULL,MS_BIND|MS_REMOUNT|MS_RDONLY|MS_NOSUID|MS_NODEV,NULL))return -1;
    return sethostname("sandbox",7);
}
static _Noreturn void guest(int input,int output,int errors,int failure) {
    int error=reset_signals();if(error)fail_child(failure,1,error);
    if(fault("pause_setup"))sleep(2);

    if(ptrace(PTRACE_TRACEME,0,NULL,NULL)||raise(SIGSTOP))fail_child(failure,1,error_number());
    if(fault("handles_fail"))fail_child(failure,3,EBADF);
    if(dup2(input,0)<0||dup2(output,1)<0||dup2(errors,2)<0||dup3(failure,3,O_CLOEXEC)<0||
       syscall(SYS_close_range,4u,UINT32_MAX,0u))fail_child(3,3,error_number());
    if(chroot(root_path)||chdir("/workspace")||setsid()<0)fail_child(3,2,error_number());
    umask(077);error=credentials();if(error||fault("credentials_fail"))fail_child(3,4,error?error:EINVAL);
    if(prctl(PR_GET_SECCOMP,0,0,0,0)!=0)fail_child(3,5,ENOTSUP);
    char *const env[]={"PATH=/usr/local/bin:/usr/bin:/bin","LANG=C.UTF-8","LC_ALL=C.UTF-8",
        "HOME=/workspace","TMPDIR=/workspace/.tmp","TZ=UTC","PYTHONDONTWRITEBYTECODE=1","PYTHONNOUSERSITE=1",NULL};
    if(fault("error_drop")||fault("error_short"))fail_child(3,6,EINVAL);
    if(prctl(PR_SET_NO_NEW_PRIVS,fault("nnp_fail")?2:1,0,0,0))fail_child(3,6,error_number());
    struct sock_fprog program={(unsigned short)(sizeof(m3_filter)/sizeof(m3_filter[0])),(struct sock_filter *)m3_filter};
    if(fault("filter_fail"))program.len=0;
    if(prctl(PR_SET_SECCOMP,SECCOMP_MODE_FILTER,&program,0,0))fail_child(3,7,error_number());
    execve(fault("exec_fail")?"/nonexistent":policy.args[0],policy.args,env);
    fail_child(3,8,error_number());
}

// §FS-workspace.results: Trusted init establishes entry from TRACEEXEC, never a guest-controlled
// string.
static _Noreturn void namespace_init(int parentfd,int report,int input,int output,int errors) {
    struct result result=result_of(SETUP,2,0,0);uint64_t sequence=0;
    int error=reset_signals();if(!error&&prctl(PR_SET_PDEATHSIG,SIGKILL,0,0,0))error=error_number();
    if(!error)error=parent_alive(parentfd);
    if(!error&&(prctl(PR_SET_DUMPABLE,0,0,0,0)||construct_root()))error=error_number();
    if(preflight&&!error){
        int saved=fcntl(report,F_DUPFD_CLOEXEC,60);unsigned stage=3;
        if(saved<0)error=error_number();else report=saved;
        if(!error&&(dup2(input,0)<0||dup2(output,1)<0||dup2(errors,2)<0||dup3(report,3,O_CLOEXEC)<0))error=error_number();
        if(!error){report=3;if(syscall(SYS_close_range,4u,UINT32_MAX,0u))error=error_number();}
        if(!error){stage=2;if(chroot(root_path)||chdir("/workspace")||setsid()<0)error=error_number();}
        if(!error){stage=4;error=credentials();}
        if(!error){stage=5;if(prctl(PR_GET_SECCOMP,0,0,0,0)!=0)error=ENOTSUP;}
        if(!error){stage=6;if(prctl(PR_SET_NO_NEW_PRIVS,1,0,0,0))error=error_number();}
        struct sock_fprog program={(unsigned short)(sizeof(m3_filter)/sizeof(m3_filter[0])),(struct sock_filter *)m3_filter};
        if(!error){stage=7;if(prctl(PR_SET_SECCOMP,SECCOMP_MODE_FILTER,&program,0,0))error=error_number();}
        result=result_of(error?SETUP:PREFLIGHT,error?stage:0,error,0);goto report;
    }
    int pipefd[2];if(!error&&pipe2(pipefd,O_CLOEXEC))error=error_number();
    if(error){result.detail=(unsigned)error;goto report;}
    int failure=fcntl(pipefd[1],F_DUPFD_CLOEXEC,60);close(pipefd[1]);
    if(failure<0){close(pipefd[0]);result.detail=(unsigned)error_number();goto report;}
    uint64_t mask=UINT64_MAX;
    if(syscall(SYS_rt_sigprocmask,SIG_SETMASK,&mask,NULL,8)){result.detail=(unsigned)error_number();close(failure);close(pipefd[0]);goto report;}
    pid_t child=fork();if(child==0)guest(input,output,errors,failure);
    close(failure);close(input);close(output);close(errors);close(parentfd);
    if(child<0){close(pipefd[0]);result.detail=(unsigned)error_number();goto report;}
    int status=0,entered=0,leader_done=0,bad=0;pid_t got;
    do { got=waitpid(child,&status,0); }while(got<0&&errno==EINTR);
    char pidtext[32];snprintf(pidtext,sizeof(pidtext),"%d",child);
    if(got!=child||!WIFSTOPPED(status)||WSTOPSIG(status)!=SIGSTOP||cg_write("cgroup.procs",pidtext)||
       ptrace(PTRACE_SETOPTIONS,child,0,PTRACE_O_TRACEEXEC|PTRACE_O_EXITKILL))bad=1;
    struct result admission=result_of(ADMITTED,0,0,0);admission.elapsed=now_ms();
    if(!bad&&send_frame(report,sequence++,admission))bad=1;
    if(!bad&&ptrace(PTRACE_CONT,child,0,0))bad=1;
    while(!bad&&!leader_done) {
        do { got=waitpid(-1,&status,__WALL); }while(got<0&&errno==EINTR);
        if(got<0){bad=1;break;}if(got!=child)continue;
        if(WIFEXITED(status)||WIFSIGNALED(status)){leader_done=1;break;}
        if(!WIFSTOPPED(status)){bad=1;break;}
        unsigned event=(unsigned)status>>16;
        if(!event&&WSTOPSIG(status)==SIGSTOP){siginfo_t info;if(ptrace(PTRACE_GETSIGINFO,child,0,&info)&&errno==EINVAL)continue;}
        if(event==PTRACE_EVENT_EXEC&&!entered){entered=1;if(send_frame(report,sequence++,result_of(ENTERED,8,0,1))){bad=1;break;}}
        if(ptrace(PTRACE_CONT,child,0,event==PTRACE_EVENT_EXEC?0:WSTOPSIG(status)))bad=1;
    }
    int leader_status=status;
    if(kill(-1,SIGKILL)&&errno!=ESRCH)bad=1;
    for(;;){got=waitpid(-1,&status,__WALL);if(got>0)continue;if(got<0&&errno==EINTR)continue;if(got<0&&errno==ECHILD)break;bad=1;break;}
    unsigned char failure_bytes[9];size_t used=0;
    while(used<sizeof(failure_bytes)){ssize_t n=read(pipefd[0],failure_bytes+used,sizeof(failure_bytes)-used);if(n<0&&errno==EINTR)continue;if(n<0){bad=1;break;}if(!n)break;used+=(size_t)n;}
    close(pipefd[0]);
    if(!bad&&!entered&&used==8&&get32(failure_bytes)>=1&&get32(failure_bytes)<=8&&get32(failure_bytes+4)>0&&get32(failure_bytes+4)<=4095)
        result=result_of(SETUP,get32(failure_bytes),get32(failure_bytes+4),0);
    else if(!bad&&entered&&!used&&leader_done&&WIFEXITED(leader_status))result=result_of(EXITED,0,WEXITSTATUS(leader_status),1);
    else if(!bad&&entered&&!used&&leader_done&&WIFSIGNALED(leader_status))result=result_of(SIGNALLED,0,WTERMSIG(leader_status),1);
    else result=result_of(UNKNOWN,9,EPROTO,entered?1:2);
report:
    result.clean=1;(void)send_frame(report,sequence,result);if(fault("exit_cancel_race"))usleep(100000);close(report);_exit(0);
}

static int capture(int fd,int destination,uint64_t cap,uint64_t *count) {
    unsigned char buffer[4096];int exceeded=0;
    for(int i=0;i<4;i++) {
        ssize_t n=read(fd,buffer,sizeof(buffer));if(n<0&&(errno==EINTR||errno==EAGAIN))break;if(n<0)return -1;if(!n)break;
        size_t keep=*count<cap?(size_t)(cap-*count):0;if(keep>(size_t)n)keep=(size_t)n;
        if(fault("output_fail")){errno=EIO;return -1;}
        if(keep&&write_all(destination,buffer,keep))return -1;
        if(*count>UINT64_MAX-(uint64_t)n)return -1;
        *count+=(uint64_t)n;
        if(*count>cap)exceeded=1;
    }
    return exceeded;
}
static int cleanup(void) {
    if(!identity_owned||!run_id||run_uid<100000||run_uid>100999)return -1;
    if(access(cgroup,F_OK)==0){uint64_t populated;if(cg_read("cgroup.events","populated",&populated)||populated)return -1;if(rmdir(cgroup))return -1;}
    else if(errno!=ENOENT)return -1;
    if(workspace_mounted){if(umount(workspace))return -1;workspace_mounted=0;}
    if(rmdir(workspace)&&errno!=ENOENT)return -1;
    if(rmdir(root_path)&&errno!=ENOENT)return -1;
    const char *names[]={"passwd","group","hostname","hosts","resolv.conf"};char path[256];
    for(unsigned i=0;i<5;i++){snprintf(path,sizeof(path),"%s/%s",run_path,names[i]);if(unlink(path)&&errno!=ENOENT)return -1;}
    int lock=open("/m3-runs/allocator",O_RDWR|O_CLOEXEC|O_NOFOLLOW);if(lock<0)return -1;
    if(flock(lock,LOCK_EX)){close(lock);return -1;}
    snprintf(path,sizeof(path),"%s/reservation",run_path);int failed=unlink(path)&&errno!=ENOENT;
    if(!failed&&rmdir(run_path))failed=1;
    int saved=errno;close(lock);errno=saved;return failed?-1:0;
}
static int setup_failure(unsigned stage,int error) {
    struct result r=result_of(SETUP,stage,error,0);r.export_state=policy.export_files?3:0;r.export_error=policy.export_files?(unsigned)error:0;
    r.clean=cleanup()==0;return finish(r);
}

// §AR-workspace.resources: Supervision remains outside the guest cgroup and services both output
// streams.
int main(int argc,char **argv) {
    int error=check_profile();if(error)return finish(result_of(SETUP,1,error,0));
    if(argc<17||(strcmp(argv[1],"M3PLAN1")&&strcmp(argv[1],"M3CHECK1")))return finish(result_of(SETUP,1,EINVAL,0));
    preflight=!strcmp(argv[1],"M3CHECK1");
    uint64_t *fields[]={&policy.memory,&policy.tasks,&policy.quota,&policy.cpu,&policy.wall,&policy.space,&policy.inodes,&policy.in,&policy.out,&policy.err};
    for(unsigned i=0;i<10;i++)if(number(argv[i+2],fields[i]))return finish(result_of(SETUP,1,EINVAL,0));
    uint64_t parent;if(number(argv[12],&parent)||!parent||parent>INT_MAX||getppid()!=(pid_t)parent)return finish(result_of(SETUP,1,ECHILD,0));
    if(strcmp(argv[13],"discard")&&strcmp(argv[13],"regular-files"))return finish(result_of(SETUP,1,EINVAL,0));
    policy.export_files=!strcmp(argv[13],"regular-files");
    tree_digest=argv[14];stdin_digest=argv[15];
    if((strcmp(tree_digest,"none")&&!digest_text(tree_digest))||(strcmp(stdin_digest,"none")&&!digest_text(stdin_digest)))return finish(result_of(SETUP,1,EINVAL,0));
    policy.args=&argv[16];
    if(strcmp(policy.args[0],"/bin/sh")&&strcmp(policy.args[0],"/usr/local/bin/python3"))return finish(result_of(SETUP,1,EINVAL,0));
    size_t bytes=0;for(int i=16;i<argc;i++){size_t n=strlen(argv[i]);if(!n||n>4096)return finish(result_of(SETUP,1,E2BIG,0));bytes+=n+1;}
    if(argc-16>64||bytes>16384||policy.memory<16777216||policy.memory>1073741824||policy.memory%4096||
       policy.tasks<4||policy.tasks>256||policy.quota<1000||policy.quota>100000||policy.cpu<10000||policy.cpu>3600000000ULL||
       policy.wall<10||policy.wall>3600000||policy.space<1048576||policy.space>268435456||policy.space%4096||
       policy.inodes<64||policy.inodes>65536||policy.in>67108864||policy.out>16777216||policy.err>16777216)
        return finish(result_of(SETUP,1,EINVAL,0));
    const char *injected=getenv("LEANCAGE_M3_TEST_MODE");if(injected)mode=injected;
    error=reset_signals();if(error)return finish(result_of(SETUP,1,error,0));
    if(fault("pause_before_arm")){char marker[128];snprintf(marker,sizeof(marker),"/m3-results/pause-%d",getpid());if(create_text(marker,"before-arm",0600))return finish(result_of(SETUP,1,error_number(),0));usleep(300000);}
    int parentfd=(int)syscall(SYS_pidfd_open,(pid_t)parent,0);
    if(parentfd<0||getppid()!=(pid_t)parent||prctl(PR_SET_PDEATHSIG,SIGKILL,0,0,0)||parent_alive(parentfd))return finish(result_of(SETUP,1,ECHILD,0));
    alarm(30);
    if(allocate_identity()){error=error_number();if(!identity_owned){run_id=0;run_uid=0;}return setup_failure(2,error);}
    if(prepare_resources()||import_tree(tree_digest))return setup_failure(2,error_number());
    if(fault("pause_before_fork")){char marker[128];snprintf(marker,sizeof(marker),"/m3-results/pause-%d",getpid());if(create_text(marker,"before-fork",0600))return setup_failure(2,error_number());usleep(300000);}
    if(record_identity(argc,argv))return setup_failure(3,error_number());
    int streams[3][2];for(int i=0;i<3;i++)if(pipe2(streams[i],O_CLOEXEC|O_NONBLOCK))return setup_failure(3,error_number());
    int input=snapshot_stdin(stdin_digest);if(input<0)return setup_failure(3,error_number());
    char path[256];int captures[2];
    for(int i=0;i<2;i++){snprintf(path,sizeof(path),"%s/%s",result_path,i?"stderr":"stdout");captures[i]=open(path,O_WRONLY|O_CREAT|O_EXCL|O_CLOEXEC,0600);if(captures[i]<0)return setup_failure(3,error_number());}
    for(int i=0;i<3;i++)if(fcntl(streams[i][1],F_SETFL,0))return setup_failure(3,error_number());
    int self=(int)syscall(SYS_pidfd_open,getpid(),0);sigset_t mask;sigemptyset(&mask);sigaddset(&mask,SIGTERM);sigaddset(&mask,SIGINT);sigaddset(&mask,SIGHUP);
    if(self<0||sigprocmask(SIG_BLOCK,&mask,NULL))return finish(result_of(SETUP,1,error_number(),0));
    int signals=signalfd(-1,&mask,SFD_CLOEXEC|SFD_NONBLOCK);if(signals<0)return finish(result_of(SETUP,1,error_number(),0));
    unsigned long flags=CLONE_NEWPID|CLONE_NEWNS|CLONE_NEWNET|CLONE_NEWIPC|CLONE_NEWUTS|SIGCHLD;
    if(fault("namespace_fail"))flags|=CLONE_THREAD;
    uint64_t launch_started=now_ms();
    pid_t init=(pid_t)syscall(SYS_clone,flags,NULL,NULL,NULL,0);
    if(!init){close(signals);for(int i=0;i<3;i++)close(streams[i][0]);namespace_init(self,streams[0][1],input,streams[1][1],streams[2][1]);}
    close(self);close(input);for(int i=0;i<3;i++)close(streams[i][1]);
    if(init<0)return setup_failure(2,error_number());
    int initfd=(int)syscall(SYS_pidfd_open,init,0);if(initfd<0){kill(init,SIGKILL);waitpid(init,NULL,0);return finish(result_of(UNKNOWN,9,error_number(),2));}
    if(fault("expose_init_pid")){char marker[256],pid[32];snprintf(marker,sizeof(marker),"%s/init.pid",result_path);snprintf(pid,sizeof(pid),"%d",init);(void)create_text(marker,pid,0400);}
    struct result result=result_of(UNKNOWN,9,EPROTO,2);unsigned char frame[FRAME_SIZE];size_t used=0;
    alarm(0);
    int admitted=0,entered=0,final=0,bad=0;uint32_t triggers=0;uint64_t sequence=0,started=launch_started,admission=0,cpu=0,peak=0,counts[2]={0,0},last_time=launch_started;
    for(;;) {
        struct pollfd fds[5]={{initfd,POLLIN,0},{streams[0][0],POLLIN|POLLHUP,0},{streams[1][0],POLLIN|POLLHUP,0},{streams[2][0],POLLIN|POLLHUP,0},{signals,POLLIN,0}};
        int n=poll(fds,5,10);if(n<0&&errno==EINTR)continue;if(n<0){bad=1;break;}
        if(fds[1].revents&(POLLIN|POLLHUP)) {
            ssize_t got=read(streams[0][0],frame+used,FRAME_SIZE-used);
            if(got>0){used+=(size_t)got;if(used==FRAME_SIZE){struct result incoming;
                if(decode_frame(frame,sequence++,&incoming))bad=1;
                else if(incoming.kind==ADMITTED&&!admitted&&!entered&&!final){admitted=1;admission=incoming.elapsed;if(admission<started||admission>now_ms())bad=1;}
                else if(incoming.kind==ENTERED&&admitted&&!entered&&!final){entered=1;guest_entered=1;}
                else if((incoming.kind<=UNKNOWN||(preflight&&incoming.kind==PREFLIGHT))&&!final){result=incoming;final=1;}
                else bad=1;
                used=0;
            }}else if(got<0&&errno!=EAGAIN&&errno!=EINTR)bad=1;
        }
        for(int i=0;i<2;i++)if(fds[i+2].revents&(POLLIN|POLLHUP)){int captured=capture(streams[i+1][0],captures[i],i?policy.err:policy.out,&counts[i]);if(captured<0){bad=1;triggers|=OUTPUT;}else if(captured)triggers|=OUTPUT;}
        if(fds[4].revents&POLLIN){struct signalfd_siginfo info;ssize_t got=read(signals,&info,sizeof(info));if(got!=(ssize_t)sizeof(info))bad=1;triggers|=REQUEST;}
        uint64_t now=now_ms();if(!now||now<last_time){bad=1;triggers|=ACCOUNTING;}last_time=now;
        if(admitted){if(now-admission>=policy.wall)triggers|=DEADLINE;uint64_t sample=0;if(cg_read("cpu.stat","usage_usec",&sample)||sample<cpu)triggers|=ACCOUNTING;else{cpu=sample;if(cpu>=policy.cpu)triggers|=CPU;}}
        else if(now-started>=30000)triggers|=SETUP_TIMEOUT;
        if(final&&fault("exit_cancel_race"))triggers|=REQUEST;
        if(triggers||bad){(void)cg_write("cgroup.kill","1");if(syscall(SYS_pidfd_send_signal,initfd,SIGKILL,NULL,0)&&errno!=ESRCH)bad=1;}
        if(fds[0].revents&POLLIN){struct pollfd p={streams[0][0],POLLIN,0};if(poll(&p,1,0)>0&&(p.revents&POLLIN))continue;break;}
    }
    if(bad){(void)cg_write("cgroup.kill","1");(void)syscall(SYS_pidfd_send_signal,initfd,SIGKILL,NULL,0);}
    int status;pid_t got;do{got=waitpid(init,&status,0);}while(got<0&&errno==EINTR);
    for(int i=0;i<2;i++){
        while(1){uint64_t before=counts[i];int r=capture(streams[i+1][0],captures[i],i?policy.err:policy.out,&counts[i]);
            if(r<0){bad=1;triggers|=OUTPUT;break;}if(r)triggers|=OUTPUT;if(before==counts[i])break;}
        if(fault("output_close_fail"))close(captures[i]);
        if(close(captures[i])){bad=1;triggers|=OUTPUT;}
    }
    uint64_t final_cpu=cpu;
    if(cg_read("cpu.stat","usage_usec",&final_cpu)||final_cpu<cpu||cg_read("memory.peak",NULL,&peak)){bad=1;triggers|=ACCOUNTING;}
    cpu=final_cpu;
    if(triggers&&!final&&!bad&&got==init&&WIFSIGNALED(status)&&WTERMSIG(status)==SIGKILL)result=result_of(CANCELLED,0,0,entered?1:2);
    else if(bad||!final||used||got!=init||!((WIFEXITED(status)&&!WEXITSTATUS(status))||(triggers&&WIFSIGNALED(status)&&WTERMSIG(status)==SIGKILL)))result=result_of(UNKNOWN,9,EPROTO,entered?1:2);
    result.cpu=cpu;result.peak=peak;result.out=counts[0];result.err=counts[1];result.triggers=triggers;uint64_t final_time=now_ms();
    if(!final_time||final_time<last_time){result.kind=UNKNOWN;result.stage=9;result.detail=EPROTO;result.triggers=triggers|ACCOUNTING;}
    else result.elapsed=final_time-(admitted?admission:started);
    if(cg_read("memory.events","oom_kill",&result.oom)||cg_read("pids.events","max",&result.pids)){result.kind=UNKNOWN;result.stage=9;result.detail=EPROTO;result.triggers|=ACCOUNTING;}
    if(!preflight&&export_workspace(&result))result.export_error=(unsigned)error_number();
    result.clean=cleanup()==0;
    if(preflight&&!result.clean){result.kind=UNKNOWN;result.stage=9;result.detail=EIO;}
    close(initfd);close(parentfd);close(signals);for(int i=0;i<3;i++)close(streams[i][0]);
    if(preflight&&result.kind==PREFLIGHT){result.run=0;result.uid=0;}
    return finish(result);
}
