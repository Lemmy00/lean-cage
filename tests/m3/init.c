// SPDX-License-Identifier: Apache-2.0
// §AR-workspace.acceptance: Disposable-VM harness reads private results, never guest console
// claims.
#define _GNU_SOURCE
#include <errno.h>
#include <net/if.h>
#include <netinet/in.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <sys/ptrace.h>
#include <sys/syscall.h>
#include <fcntl.h>
#include <inttypes.h>
#include <signal.h>
#include <poll.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/io.h>
#include <sys/ipc.h>
#include <sys/mount.h>
#include <sys/reboot.h>
#include <sys/shm.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <time.h>
#include <sys/utsname.h>
#include <sys/wait.h>
#include <unistd.h>

static uint32_t get32(const unsigned char *p){uint32_t n=0;for(int i=0;i<4;i++)n|=(uint32_t)p[i]<<(i*8);return n;}
static uint64_t get64(const unsigned char *p){uint64_t n=0;for(int i=0;i<8;i++)n|=(uint64_t)p[i]<<(i*8);return n;}
static int write_control(const char *path,const char *text){int fd=open(path,O_WRONLY);if(fd<0)return -1;ssize_t n=write(fd,text,strlen(text));close(fd);return n==(ssize_t)strlen(text)?0:-1;}
#include "../../native/m3_sha256.h"
struct testcase {
    const char *name,*exe,*code,*tree,*stdin,*fault,*expected;
    int kind,detail,entry,clean,triggers,export_state,omitted,check,oom,pids;
    uint64_t memory,tasks,quota,cpu,wall,space,inodes,in_cap,out_cap,err_cap;
};
#include "cases.h"
static pid_t sentinel;
static int sentinel_fd=-1;
static int sentinel_alive(void){struct pollfd p={sentinel_fd,POLLIN,0};return sentinel_fd>=0&&poll(&p,1,0)==0&&kill(sentinel,0)==0;}
static uint64_t millis(void){struct timespec t;if(clock_gettime(CLOCK_MONOTONIC,&t))return 0;return (uint64_t)t.tv_sec*1000+(uint64_t)t.tv_nsec/1000000;}
static int file_hash(const char *path,char digest[65],char prefix[8193],uint64_t *size) {
    int fd=open(path,O_RDONLY|O_NOFOLLOW);if(fd<0)return -1;
    struct m3_sha hash;sha_init(&hash);unsigned char data[4096];*size=0;size_t kept=0;
    for(;;){ssize_t n=read(fd,data,sizeof(data));if(n<0&&errno==EINTR)continue;if(n<0){close(fd);return -1;}if(!n)break;
        sha_update(&hash,data,(size_t)n);*size+=(uint64_t)n;
        for(ssize_t i=0;i<n&&kept<4096;i++,kept++){prefix[2*kept]="0123456789abcdef"[data[i]>>4];prefix[2*kept+1]="0123456789abcdef"[data[i]&15];}
    }
    prefix[kept*2]=0;unsigned char bytes[32];sha_final(&hash,bytes);sha_hex(bytes,digest);close(fd);return 0;
}
static int run_case(const struct testcase *c) {
    uint64_t began=millis();
    printf("M3_CASE_BEGIN name=%s\n",c->name);
    int reports[2];if(pipe2(reports,O_CLOEXEC))return 1;
    char parent[32],numbers[10][32];snprintf(parent,sizeof(parent),"%d",getpid());
    uint64_t limits[]={c->memory,c->tasks,c->quota,c->cpu,c->wall,c->space,c->inodes,c->in_cap,c->out_cap,c->err_cap};
    for(int i=0;i<10;i++)snprintf(numbers[i],32,"%"PRIu64,limits[i]);
    pid_t child=fork();if(child<0)return 1;
    if(!child){
        int alias=open("/",O_RDONLY|O_DIRECTORY);if(alias<0||dup2(alias,31)<0)_exit(119);close(alias);
        if(dup2(reports[1],1)<0)_exit(120);
        close(reports[0]);close(reports[1]);
        char mode[128];snprintf(mode,sizeof(mode),"LEANCAGE_M3_TEST_MODE=%s",c->fault[0]?c->fault:"normal");
        char *const args[]={"/leancage-m3-helper",c->check?"M3CHECK1":"M3PLAN1",numbers[0],numbers[1],numbers[2],numbers[3],numbers[4],numbers[5],numbers[6],numbers[7],numbers[8],numbers[9],parent,c->export_state?"regular-files":"discard",(char *)c->tree,(char *)c->stdin,(char *)c->exe,"-c",(char *)c->code,NULL};
        char *const environment[]={"LC_ALL=C",mode,NULL};execve(args[0],args,environment);_exit(121);
    }
    close(reports[1]);unsigned char frame[161]={0};size_t used=0;
    while(used<sizeof(frame)){ssize_t n=read(reports[0],frame+used,sizeof(frame)-used);if(n<0&&errno==EINTR)continue;if(n<=0)break;used+=(size_t)n;}
    close(reports[0]);int status;if(waitpid(child,&status,0)!=child)return 1;
    int exit_code=WIFEXITED(status)?WEXITSTATUS(status):WIFSIGNALED(status)?128+WTERMSIG(status):255;
    uint64_t run=get64(frame+8);unsigned uid=get32(frame+52),detail=get32(frame+36);
    int observed_kill=c->kind==3&&frame[6]==2&&detail==SIGKILL;
    int valid=used==160&&!memcmp(frame,"LC3R",4)&&frame[4]==1&&frame[5]==0&&frame[7]==0&&
        get64(frame+16)==0&&get32(frame+24)==128&&!get32(frame+28)&&!get32(frame+156)&&
        (frame[6]==c->kind||observed_kill)&&(observed_kill||(c->detail<0?detail>0:detail==(unsigned)c->detail))&&get32(frame+40)==(unsigned)c->entry&&get32(frame+44)==(unsigned)c->clean&&
        (c->triggers?(get32(frame+48)&c->triggers)==(unsigned)c->triggers:!get32(frame+48))&&
        get32(frame+96)==(unsigned)c->export_state&&get32(frame+100)==(unsigned)c->omitted&&
        (!c->oom||get64(frame+136)>0)&&(!c->pids||get64(frame+144)>0);
    int expected_exit=observed_kill?128+SIGKILL:c->kind==0?c->detail:c->kind==1?125:c->kind==2?128+c->detail:c->kind==3?124:c->kind==7?0:126;
    if(exit_code!=expected_exit)valid=0;
    char path[256],out_hash[65]="",err_hash[65]="",out_prefix[8193]="",err_prefix[8193]="";uint64_t out_size=0,err_size=0;
    if(run&&c->entry){
        snprintf(path,sizeof(path),"/m3-results/%"PRIu64"/stdout",run);if(file_hash(path,out_hash,out_prefix,&out_size))valid=0;
        snprintf(path,sizeof(path),"/m3-results/%"PRIu64"/stderr",run);if(file_hash(path,err_hash,err_prefix,&err_size))valid=0;
        int output_lost=frame[6]==4&&(get32(frame+48)&8);
        if(out_size>c->out_cap||err_size>c->err_cap||out_size>get64(frame+72)||err_size>get64(frame+80)||
           (!output_lost&&(out_size!=(get64(frame+72)<c->out_cap?get64(frame+72):c->out_cap)||err_size!=(get64(frame+80)<c->err_cap?get64(frame+80):c->err_cap))))valid=0;
        if(c->expected[0]){struct m3_sha h;unsigned char b[32];char expected[65];sha_init(&h);sha_update(&h,c->expected,strlen(c->expected));sha_final(&h,b);sha_hex(b,expected);if(strcmp(out_hash,expected))valid=0;}
    }
    int export_ok=0;
    if(c->export_state==1){char hash[65],prefix[8193],expected[65];uint64_t size;snprintf(path,sizeof(path),"/m3-results/%"PRIu64"/export.manifest",run);sha_hex(frame+104,expected);
        export_ok=!file_hash(path,hash,prefix,&size)&&!strcmp(hash,expected);if(!export_ok)valid=0;
        printf("M3_EXPORT name=%s sha256=%s bytes=%"PRIu64" prefix_hex=%s\n",c->name,hash,size,prefix);
    }
    int extinct=1;
    if(run){snprintf(path,sizeof(path),"/sys/fs/cgroup/m3/%"PRIu64,run);if(access(path,F_OK)==0||errno!=ENOENT)extinct=0;snprintf(path,sizeof(path),"/m3-runs/%u",uid);if(access(path,F_OK)==0||errno!=ENOENT)extinct=0;}
    int alive=sentinel_alive();if(!alive||!extinct)valid=0;
    printf("M3_RESULT {\"name\":\"%s\",\"frame_bytes\":%zu,\"kind\":%u,\"stage\":%u,\"detail\":%u,\"entry\":%u,\"clean\":%u,\"triggers\":%u,\"run\":%"PRIu64",\"uid\":%u,\"cpu\":%"PRIu64",\"peak\":%"PRIu64",\"out\":%"PRIu64",\"err\":%"PRIu64",\"elapsed\":%"PRIu64",\"oom\":%"PRIu64",\"pids\":%"PRIu64",\"export\":%u,\"omitted\":%u,\"export_valid\":%d,\"stdout_sha256\":\"%s\",\"stderr_sha256\":\"%s\",\"stdout_stored\":%"PRIu64",\"stderr_stored\":%"PRIu64",\"stdout_prefix_hex\":\"%s\",\"stderr_prefix_hex\":\"%s\",\"began\":%"PRIu64",\"ended\":%"PRIu64",\"exit\":%d,\"sentinel\":%d,\"extinct\":%d,\"valid\":%d}\n",
        c->name,used,frame[6],get32(frame+32),detail,get32(frame+40),get32(frame+44),get32(frame+48),run,uid,get64(frame+56),get64(frame+64),get64(frame+72),get64(frame+80),get64(frame+88),get64(frame+136),get64(frame+144),get32(frame+96),get32(frame+100),export_ok,out_hash,err_hash,out_size,err_size,out_prefix,err_prefix,began,millis(),exit_code,alive,extinct,valid);
    return !valid;
}
static int read_counter(uint64_t *value) {
    int fd=open("/m3-runs/allocator",O_RDONLY);unsigned char data[8];if(fd<0)return -1;ssize_t n=read(fd,data,8);close(fd);if(n!=8)return -1;*value=get64(data);return 0;
}
static int death_case(const char *name,int controller_death,int early,int cancel) {
    uint64_t previous;if(read_counter(&previous))return 1;
    int report[2],identity[2];if(pipe2(report,O_CLOEXEC)||pipe2(identity,O_CLOEXEC))return 1;
    pid_t controller=fork();if(controller<0)return 1;
    if(!controller){
        close(report[0]);close(identity[0]);char parent[32];snprintf(parent,sizeof(parent),"%d",getpid());
        pid_t helper=fork();if(helper<0)_exit(120);
        if(!helper){if(dup2(report[1],1)<0)_exit(120);close(report[1]);close(identity[1]);
            char *const args[]={"/leancage-m3-helper","M3PLAN1","268435456","32","100000","10000000","10000","16777216","1024","0","1048576","1048576",parent,"discard","none","none","/bin/sh","-c","printf ready; sleep 100",NULL};
            char *const environment[]={"LC_ALL=C",early?(controller_death==1?"LEANCAGE_M3_TEST_MODE=pause_before_arm":"LEANCAGE_M3_TEST_MODE=pause_before_fork"):controller_death==2?"LEANCAGE_M3_TEST_MODE=expose_init_pid":"LEANCAGE_M3_TEST_MODE=normal",NULL};execve(args[0],args,environment);_exit(121);
        }
        if(write(identity[1],&helper,sizeof(helper))!=sizeof(helper))_exit(120);
        close(identity[1]);close(report[1]);int status;if(waitpid(helper,&status,0)!=helper)_exit(120);_exit(0);
    }
    close(report[1]);close(identity[1]);pid_t helper;if(read(identity[0],&helper,sizeof(helper))!=sizeof(helper))return 1;close(identity[0]);
    uint64_t run=0;int ready=0;char path[256];
    if(early){snprintf(path,sizeof(path),"/m3-results/pause-%d",helper);for(unsigned i=0;i<1000;i++){if(!access(path,F_OK)){ready=1;break;}usleep(1000);}}
    else for(unsigned i=0;i<1000;i++){uint64_t latest;
        if(!read_counter(&latest)&&latest>previous){run=latest;snprintf(path,sizeof(path),"/m3-results/%"PRIu64"/stdout",run);int fd=open(path,O_RDONLY);char data[5];if(fd>=0){ssize_t n=read(fd,data,5);close(fd);if(n==5&&!memcmp(data,"ready",5)){ready=1;break;}}}
        usleep(10000);
    }
    int target=controller_death==1?controller:helper;
    if(controller_death==2){snprintf(path,sizeof(path),"/m3-results/%"PRIu64"/init.pid",run);int fd=open(path,O_RDONLY);char children[128]={0};ssize_t n=fd<0?-1:read(fd,children,sizeof(children)-1);if(fd>=0)close(fd);if(n<=0)return 1;target=atoi(children);if(target<=1)return 1;}
    int targetfd=(int)syscall(SYS_pidfd_open,target,0);int failed=!ready||targetfd<0||syscall(SYS_pidfd_send_signal,targetfd,cancel?SIGTERM:SIGKILL,NULL,0);if(targetfd>=0)close(targetfd);
    int status;if(waitpid(controller,&status,0)!=controller)failed=1;
    unsigned char frame[161];size_t used=0;
    while(used<sizeof(frame)){ssize_t n=read(report[0],frame+used,sizeof(frame)-used);if(n<0&&errno==EINTR)continue;if(n<=0)break;used+=(size_t)n;}
    close(report[0]);uint64_t latest;if(!read_counter(&latest)&&latest>previous)run=latest;
    int extinct=0,quarantined=0;
    for(unsigned i=0;i<200;i++){
        while(waitpid(-1,NULL,WNOHANG)>0){}
        if(!run){extinct=1;break;}
        snprintf(path,sizeof(path),"/sys/fs/cgroup/m3/%"PRIu64"/cgroup.events",run);int fd=open(path,O_RDONLY);char text[128]={0};ssize_t n=fd<0?-1:read(fd,text,sizeof(text)-1);if(fd>=0)close(fd);
        if((fd<0&&errno==ENOENT)||(n>0&&strstr(text,"populated 0\n"))){extinct=1;quarantined=fd>=0;break;}
        usleep(10000);
    }
    int private_ok=controller_death==2?(used==160&&frame[6]==4&&get32(frame+40)==1&&get32(frame+44)==1):cancel?(used==160&&frame[6]==3&&get32(frame+40)==1&&get32(frame+44)==1&&(get32(frame+48)&1)):(used==0||(early&&controller_death&&used==160&&frame[6]==1&&get32(frame+40)==0&&get64(frame+8)==0));
    int alive=sentinel_alive();failed|=!extinct||!private_ok||!alive;
    printf("M3_DEATH {\"name\":\"%s\",\"ready\":%d,\"frame_bytes\":%zu,\"run\":%"PRIu64",\"extinct\":%d,\"quarantined\":%d,\"sentinel\":%d,\"private_ok\":%d,\"valid\":%d}\n",name,ready,used,run,extinct,quarantined,alive,private_ok,!failed);
    return failed;
}
static int parallel_cases(void) {
    pid_t workers[2];char path[64];
    for(unsigned i=0;i<2;i++){
        snprintf(path,sizeof(path),"/parallel-%u",i);int fd=open(path,O_WRONLY|O_CREAT|O_EXCL,0600);if(fd<0)return 1;
        workers[i]=fork();if(workers[i]<0)return 1;
        if(!workers[i]){if(dup2(fd,1)<0)_exit(120);close(fd);const struct testcase *c=&cases[sizeof(cases)/sizeof(cases[0])-2+i];_exit(run_case(c));}close(fd);
    }
    int failed=0;
    for(unsigned i=0;i<2;i++){int status;if(waitpid(workers[i],&status,0)!=workers[i]||status)failed=1;
        snprintf(path,sizeof(path),"/parallel-%u",i);int fd=open(path,O_RDONLY);if(fd<0)return 1;char buffer[4096];ssize_t n;
        while((n=read(fd,buffer,sizeof(buffer)))>0)if(fwrite(buffer,1,(size_t)n,stdout)!=(size_t)n)failed=1;
        close(fd);
    }return failed;
}
static int api_case(const char *name,const char *command,const char *argument,char *saved,size_t capacity) {
    int pipefd[2];if(pipe2(pipefd,O_CLOEXEC))return 1;pid_t child=fork();if(child<0)return 1;
    if(!child){if(dup2(pipefd[1],1)<0||dup2(pipefd[1],2)<0)_exit(120);close(pipefd[0]);close(pipefd[1]);execl("/leancage","leancage",command,argument,(char *)NULL);_exit(121);}
    close(pipefd[1]);size_t used=0;
    while(used<capacity-1){ssize_t n=read(pipefd[0],saved+used,capacity-1-used);if(n<0&&errno==EINTR)continue;if(n<=0)break;used+=(size_t)n;}
    close(pipefd[0]);saved[used]=0;int status;if(waitpid(child,&status,0)!=child)return 1;
    printf("M3_API name=%s exit=%d json_hex=",name,WIFEXITED(status)?WEXITSTATUS(status):255);
    for(size_t i=0;i<used;i++)printf("%02x",(unsigned char)saved[i]);
    putchar('\n');
    return status!=0||!used||used==capacity-1;
}
static int api_cases(void) {
    char check[8192],run[8192],report[8192],id[32];int failed=api_case("check","check","/api-policy.json",check,sizeof(check));
    failed|=api_case("run","run","/api-policy.json",run,sizeof(run));
    int fd=open("/m3-runs/allocator",O_RDONLY);unsigned char bytes[8];if(fd<0||read(fd,bytes,8)!=8)return 1;close(fd);snprintf(id,sizeof(id),"%"PRIu64,get64(bytes));
    failed|=api_case("report","report",id,report,sizeof(report));
    if(strcmp(run,report)||!strstr(check,"preflight_supported")||!strstr(run,"\"entry\":\"yes\""))failed=1;
    return failed;
}
// §AR-workspace.acceptance: Actual peers transfer bytes; merely creating a socket is insufficient.
static int network_control(int domain) {
    int server=socket(domain,SOCK_STREAM,0),client=-1,peer=-1,result=-1;char byte=0;
    struct sockaddr_storage address={0};socklen_t length;
    if(domain==AF_INET){struct sockaddr_in *a=(void *)&address;a->sin_family=AF_INET;a->sin_addr.s_addr=htonl(INADDR_LOOPBACK);length=sizeof(*a);}
    else{struct sockaddr_in6 *a=(void *)&address;a->sin6_family=AF_INET6;a->sin6_addr=in6addr_loopback;length=sizeof(*a);}
    if(server<0||bind(server,(void *)&address,length)||getsockname(server,(void *)&address,&length)||listen(server,1))goto out;
    client=socket(domain,SOCK_STREAM,0);if(client<0||connect(client,(void *)&address,length))goto out;
    peer=accept(server,NULL,NULL);if(peer<0||write(client,"N",1)!=1||read(peer,&byte,1)!=1||byte!='N')goto out;
    result=0;
out:
    if(peer>=0)close(peer);
    if(client>=0)close(client);
    if(server>=0)close(server);
    return result;
}
static int controls(void) {
    int control=socket(AF_INET,SOCK_DGRAM,0);struct ifreq request={0};strcpy(request.ifr_name,"lo");
    if(control<0||ioctl(control,SIOCGIFFLAGS,&request))return -1;
    request.ifr_flags|=IFF_UP;if(ioctl(control,SIOCSIFFLAGS,&request)){close(control);return -1;}close(control);
    if(network_control(AF_INET)||network_control(AF_INET6))return -1;
    int pair[2];char byte=0;if(socketpair(AF_UNIX,SOCK_STREAM,0,pair)||write(pair[0],"U",1)!=1||read(pair[1],&byte,1)!=1||byte!='U')return -1;
    close(pair[0]);close(pair[1]);
    int id=shmget(IPC_PRIVATE,4096,IPC_CREAT|0600);if(id<0)return -1;
    char *shared=shmat(id,NULL,0);if(shared==(void *)-1)return -1;shared[0]='I';
    pid_t child=fork();if(child<0)return -1;if(!child){if(shared[0]!='I')_exit(1);shared[0]='P';_exit(0);}int status;
    if(waitpid(child,&status,0)!=child||status||shared[0]!='P'||shmdt(shared)||shmctl(id,IPC_RMID,NULL))return -1;
    if(mkdir("/dev/shm",0700)||mount("tmpfs","/dev/shm","tmpfs",MS_NOSUID|MS_NODEV,"size=65536"))return -1;
    int fd=shm_open("/m3-control",O_CREAT|O_EXCL|O_RDWR,0600);if(fd<0||ftruncate(fd,4096))return -1;
    shared=mmap(NULL,4096,PROT_READ|PROT_WRITE,MAP_SHARED,fd,0);if(shared==MAP_FAILED)return -1;shared[0]='S';
    child=fork();if(child<0)return -1;if(!child){if(shared[0]!='S')_exit(1);shared[0]='V';_exit(0);}
    if(waitpid(child,&status,0)!=child||status||shared[0]!='V'||munmap(shared,4096)||shm_unlink("/m3-control"))return -1;
    close(fd);
    child=fork();if(child<0)return -1;if(!child){if(ptrace(PTRACE_TRACEME,0,0,0))_exit(1);raise(SIGSTOP);_exit(0);}
    if(waitpid(child,&status,0)!=child||!WIFSTOPPED(status)||ptrace(PTRACE_CONT,child,0,0)||waitpid(child,&status,0)!=child||status)return -1;
    return 0;
}
int main(void) {
    if(getpid()!=1)return 99;
    if(mount("proc","/proc","proc",MS_NOSUID|MS_NODEV|MS_NOEXEC,NULL)||mount("sysfs","/sys","sysfs",MS_NOSUID|MS_NODEV|MS_NOEXEC,NULL))return 98;
    setvbuf(stdout,NULL,_IONBF,0);
    struct utsname uts;if(uname(&uts)||strcmp(uts.release,"6.18.59"))return 97;
    printf("M3_PROFILE kernel=%s uid=%u\n",uts.release,getuid());
    mkdir("/sys/fs/cgroup",0755);
    if(mount("cgroup2","/sys/fs/cgroup","cgroup2",0,NULL)||
       write_control("/sys/fs/cgroup/cgroup.subtree_control","+memory +pids +cpu")||mkdir("/sys/fs/cgroup/m3",0755)||
       write_control("/sys/fs/cgroup/m3/cgroup.subtree_control","+memory +pids +cpu")){printf("M3_CONTROL cgroup_error=%d\n",errno);return 96;}
    if(mount("/m3-runtime","/m3-runtime",NULL,MS_BIND,NULL)||mount(NULL,"/m3-runtime",NULL,MS_BIND|MS_REMOUNT|MS_RDONLY|MS_NOSUID|MS_NODEV,NULL)){printf("M3_CONTROL runtime_error=%d\n",errno);return 95;}
    if(controls()){printf("M3_CONTROL failure=%d\n",errno);return 94;}
    puts("M3_CONTROL unix=roundtrip ipv4=roundtrip ipv6=roundtrip sysvipc=roundtrip posixshm=roundtrip ptrace=working cgroup=present runtime_readonly=1");
    sentinel=fork();if(sentinel<0)return 92;if(!sentinel)for(;;)pause();
    sentinel_fd=(int)syscall(SYS_pidfd_open,sentinel,0);if(sentinel_fd<0)return 91;
    int failures=0;size_t count=sizeof(cases)/sizeof(cases[0]);
    for(size_t i=0;i<count-2;i++)failures+=run_case(&cases[i]);
    failures+=parallel_cases();failures+=api_cases();
    failures+=death_case("cancel_after_entry",0,0,1);
    failures+=death_case("helper_death",0,0,0);
    failures+=death_case("controller_death",1,0,0);
    failures+=death_case("init_death",2,0,0);
    failures+=death_case("helper_before_fork",0,1,0);
    failures+=death_case("controller_before_arm",1,1,0);
    printf("M3_COMPLETE cases=%zu failures=%d\n",count,failures);kill(sentinel,SIGKILL);waitpid(sentinel,NULL,0);
    if(ioperm(0xf4,4,1)==0)outl(failures?0x11:0x10,0xf4);
    reboot(RB_POWER_OFF);return failures;
}
