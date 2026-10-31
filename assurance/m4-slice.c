/* SPDX-License-Identifier: Apache-2.0 */
#include "abi.h"
enum  {
    EXITED,
    SETUP,
    SIGNALLED,
    CANCELLED,
    UNKNOWN,
    ADMITTED,
    ENTERED,
    PREFLIGHT
};
struct result  {
    uint32_t kind,
    stage,
    detail,
    entry,
    clean,
    triggers,
    uid;
    uint64_t run,
    cpu,
    peak,
    out,
    err,
    elapsed,
    oom,
    pids;
    uint32_t export_state,
    omitted,
    export_error;
    unsigned char export_digest[32];
};
static uint64_t run_id;
static const char *mode="normal";
enum  {
    FRAME_SIZE=160
};
static int preflight;
static unsigned run_uid;
static int fault(const char *name)  {
    return strcmp(mode,name)==0;
}
static int error_number(void)  {
    return errno>0 && errno<=4095?errno:EIO;
}
static int write_all(int fd,const void *data,size_t count)  {
    const unsigned char *p=data;
    while(count)  {
        ssize_t n=write(fd,p,count);
        if(n<0&&errno==EINTR)continue;
        if(n<=0)return -1;
        p+=n;
        count-=(size_t)n;
    }
    return 0;
}
static void put32(unsigned char *p,uint32_t x)  {
    for(int i=0;i<4;i++)p[i]=(unsigned char)(x>>(8*i));
}
static void put64(unsigned char *p,uint64_t x)  {
    for(int i=0;i<8;i++)p[i]=(unsigned char)(x>>(8*i));
}
static uint32_t get32(const unsigned char *p)  {
    uint32_t x=0;
    for(int i=0;i<4;i++)x|=(uint32_t)p[i]<<(8*i);
    return x;
}
static uint64_t get64(const unsigned char *p)  {
    uint64_t x=0;
    for(int i=0;i<8;i++)x|=(uint64_t)p[i]<<(8*i);
    return x;
}
static int send_frame(int fd,uint64_t sequence,struct result result)  {
    unsigned char bytes[FRAME_SIZE]= {
        0
    };
    memcpy(bytes,"LC3R",4);
    bytes[4]=1;
    bytes[6]=(unsigned char)result.kind;
    put64(bytes+8,result.run);
    put64(bytes+16,sequence);
    put32(bytes+24,FRAME_SIZE-32);
    put32(bytes+32,result.stage);
    put32(bytes+36,result.detail);
    put32(bytes+40,result.entry);
    put32(bytes+44,result.clean);
    put32(bytes+48,result.triggers);
    put32(bytes+52,result.uid);
    put64(bytes+56,result.cpu);
    put64(bytes+64,result.peak);
    put64(bytes+72,result.out);
    put64(bytes+80,result.err);
    put64(bytes+88,result.elapsed);
    put32(bytes+96,result.export_state);
    put32(bytes+100,result.omitted);
    memcpy(bytes+104,result.export_digest,32);
    put64(bytes+136,result.oom);
    put64(bytes+144,result.pids);
    put32(bytes+152,result.export_error);
    if(fd!=1&&result.kind<=UNKNOWN&&fault("report_wrong_seq"))put64(bytes+16,sequence+1);
    if(fd!=1&&result.kind<=UNKNOWN&&fault("report_bad_reserved"))bytes[28]=1;
    if(fd!=1&&result.kind<=UNKNOWN&&fault("report_duplicate")) {
        if(write_all(fd,bytes,sizeof(bytes)))return -1;
    }
    if(fd!=1&&result.kind<=UNKNOWN&&fault("report_short"))return write_all(fd,bytes,17);
    if(fd!=1&&result.kind<=UNKNOWN&&fault("report_drop"))return 0;
    return write_all(fd,bytes,sizeof(bytes));
}
static int decode_frame(const unsigned char *p,uint64_t sequence,struct result *r)  {
    if(memcmp(p,"LC3R",4)||p[4]!=1||p[5]||p[7]||get64(p+8)!=run_id|| get64(p+16)!=sequence||
    get32(p+24)!=FRAME_SIZE-32||get32(p+28))return -1;
    for(int i=156;i<FRAME_SIZE;i++)if(p[i])return -1;
    *r=(struct result) {
        .kind=p[6],
        .stage=get32(p+32),
        .detail=get32(p+36),
        .entry=get32(p+40),
        .clean=get32(p+44),
        .triggers=get32(p+48),
        .uid=get32(p+52),
        .run=get64(p+8),
        .cpu=get64(p+56),
        .peak=get64(p+64),
        .out=get64(p+72),
        .err=get64(p+80),
        .elapsed=get64(p+88)
    };
    if(r->kind>PREFLIGHT||r->entry>2||r->clean>1||r->uid!=run_uid||r->triggers||
    r->cpu||r->peak||r->out||r->err)return -1;
    for(int i=96;i<156;i++)if(p[i])return -1;
    switch(r->kind) {
        case EXITED: if(r->stage||r->detail>255||r->entry!=1) return -1;
        break;
        case SETUP: if(r->stage<1||r->stage>8||!r->detail||r->detail>4095||r->entry) return -1;
        break;
        case SIGNALLED: if(r->stage||!r->detail||r->detail>64||r->entry!=1)return -1;
        break;
        case UNKNOWN: if(r->stage!=9||!r->detail||r->detail>4095)return -1;
        break;
        case ADMITTED: if(r->stage||r->detail||r->entry||r->clean||!r->elapsed)return -1;
        break;
        case ENTERED: if(r->stage!=8||r->detail||r->entry!=1||r->clean)return -1;
        break;
        case PREFLIGHT: if(!preflight||r->stage||r->detail||r->entry)return -1;
        break;
        default:return -1;
    }
    return 0;
}
static struct result result_of(unsigned kind,unsigned stage,unsigned detail,unsigned entry)
{
    return (struct result) {
        .kind=kind,
        .stage=stage,
        .detail=detail,
        .entry=entry,
        .run=run_id,
        .uid=run_uid
    };
}
static _Noreturn void fail_child(int fd,unsigned stage,int error)  {
    unsigned char bytes[8];
    put32(bytes,stage);
    put32(bytes+4,(uint32_t)error);
    if(!fault("error_drop")) (void)write_all(fd,bytes,fault("error_short")?3:8);
    _exit(125);
}
static int finish(struct result result)  {
    (void)send_frame(1,0,result);
    if(result.kind==PREFLIGHT)return 0;
    if(result.kind==EXITED)return (int)result.detail;
    if(result.kind==SIGNALLED)return 128+(int)result.detail;
    return result.kind==SETUP?125:result.kind==CANCELLED?124:126;
}
struct result m4_collect_failure(int fd,int bad,int entered,int leader_done,int leader_status)
{
    int pipefd[1]= {
        fd
    };
    struct result result;
    unsigned char failure_bytes[9];
    size_t used=0;
    while(used<sizeof(failure_bytes)) {
        ssize_t n=read(pipefd[0],failure_bytes+used,sizeof(failure_bytes)-used);
        if(n<0&&errno==EINTR)continue;
        if(n<0) {
            bad=1;
            break;
        }
        if(!n)break;
        used+=(size_t)n;
    }
    close(pipefd[0]);
    if(!bad&&!entered&&used==8&&get32(failure_bytes)>=1&&get32(failure_bytes)<=8&&
    get32(failure_bytes+4)>0&&get32(failure_bytes+4)<=4095) result=result_of(SETUP,get32(failure_bytes),
    get32(failure_bytes+4),0);
    else if(!bad&&entered&&!used&&leader_done&&WIFEXITED(leader_status))result=result_of(EXITED,
    0,WEXITSTATUS(leader_status),1);
    else if(!bad&&entered&&!used&&leader_done&&WIFSIGNALED(leader_status))result=result_of(SIGNALLED,
    0,WTERMSIG(leader_status),1);
    else result=result_of(UNKNOWN,9,EPROTO,entered?1:2);
    return result;
}
void (*m4_roots[])(void) =  {
    (void (*)(void))fault,
    (void (*)(void))error_number,
    (void (*)(void))write_all,
    (void (*)(void))put32,
    (void (*)(void))put64,
    (void (*)(void))get32,
    (void (*)(void))get64,
    (void (*)(void))send_frame,
    (void (*)(void))decode_frame,
    (void (*)(void))result_of,
    (void (*)(void))fail_child,
    (void (*)(void))finish
};
