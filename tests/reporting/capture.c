// SPDX-License-Identifier: Apache-2.0
// §AR-workspace.transport: Exercise the maintained collector and encoder with scripted I/O.
// Only read/write are replaced; the helper entry point is never executed on the host.
#define read reporting_read
#define write reporting_write
#define close reporting_close
#define main unused_helper_main
// §FS-entry.runtime: Enable scripted test faults; the helper's VM entry is never invoked here.
#define LEANCAGE_ENTRY_TEST 1
#ifndef HELPER_SOURCE
#define HELPER_SOURCE "../../linux/workspace.c"
#endif
#include HELPER_SOURCE
#undef main
#undef write
#undef read
#undef close
#ifndef LEGACY_CAPTURE
#include "../../linux/entry_decimal.c"
#include "../../linux/entry_handles.c"
#include "../../linux/process_primitives.c"
#endif
#include <assert.h>

struct read_event { const char *bytes; ssize_t result; int error; size_t touched; };
struct write_event { ssize_t result; int error; };
static const struct read_event *reads;
static const struct write_event *writes;
static size_t read_used,read_length,write_used,write_length,stored,framed;
static unsigned char output[64],frame_output[160];
static int capture_destination;

int reporting_close(int fd) { assert(fd==12);return 0; }

ssize_t reporting_read(int fd,void *buffer,size_t capacity) {
    assert(fd==11 && capacity==4096);
    if(read_used==read_length)return 0;
    struct read_event event=reads[read_used++];
    assert(event.touched<=capacity);
    if(event.touched)memcpy(buffer,event.bytes,event.touched);
    if(event.result<0)errno=event.error;
    else assert((size_t)event.result<=event.touched);
    return event.result;
}

ssize_t reporting_write(int fd,const void *buffer,size_t count) {
    if(fd==1){assert(framed+count<=sizeof(frame_output));memcpy(frame_output+framed,buffer,count);framed+=count;return (ssize_t)count;}
    assert(fd==12);
    ssize_t n=(ssize_t)count;
    if(write_used<write_length){struct write_event event=writes[write_used++];n=event.result;if(n<0)errno=event.error;}
    if(n>0){assert((size_t)n<=count && stored+(size_t)n<=sizeof(output));memcpy(output+stored,buffer,(size_t)n);stored+=(size_t)n;}
    return n;
}

static void reset(const struct read_event *input,size_t ni,const struct write_event *storage,size_t no) {
    reads=input;read_length=ni;read_used=0;writes=storage;write_length=no;write_used=0;stored=0;framed=0;mode="normal";
    memset(output,0,sizeof(output));memset(frame_output,0,sizeof(frame_output));capture_destination=12;
}

static int collect(uint64_t cap,uint64_t *observed,int *failed) {
#ifdef LEGACY_CAPTURE
    (void)failed;
    return capture(11,12,cap,observed);
#else
    int result=capture(11,&capture_destination,cap,observed);
    *failed=capture_destination<0;
    return result;
#endif
}

static void short_transfers(void) {
    const struct read_event input[]={{"ABCD",4,0,4},{"",-1,EAGAIN,0},{"EFGH",4,0,4}};
    const struct write_event storage[]={{1,0},{-1,EINTR},{2,0},{1,0}};
    uint64_t observed=0;int failed=0;reset(input,3,storage,4);
    assert(collect(6,&observed,&failed)==0 && observed==4 && !failed);
    assert(collect(6,&observed,&failed)==1 && observed==8 && !failed);
    assert(stored==6 && !memcmp(output,"ABCDEF",6));
}

static void zero_capacity(void) {
    const struct read_event input[]={{"ABCD",4,0,4}};
    uint64_t observed=0;int failed=0;reset(input,1,NULL,0);
    assert(collect(0,&observed,&failed)==1 && observed==4 && !failed && !stored);
}

static void retry_read(void) {
    const struct read_event input[]={{"noise",-1,EINTR,5},{"AB",2,0,2}};
    uint64_t observed=0;int failed=0;reset(input,2,NULL,0);
    assert(collect(4,&observed,&failed)==0 && !observed && !stored && !failed);
    assert(collect(4,&observed,&failed)==0 && observed==2 && stored==2 && !failed);
    assert(!memcmp(output,"AB",2));
}

static void partial_read_fault(void) {
    const struct read_event input[]={{"ABnoise",2,0,7},{"discard",-1,EFAULT,7},{"CD",2,0,2}};
    uint64_t observed=0;int failed=0;reset(input,3,NULL,0);
    assert(collect(8,&observed,&failed)==-1 && observed==2 && failed);
    assert(stored==2 && !memcmp(output,"AB",2));
    assert(collect(8,&observed,&failed)==0 && observed==4 && failed && stored==2);
}

static void overflow(void) {
    const struct read_event input[]={{"ABCD",4,0,4},{"EFGH",4,0,4}};
    uint64_t observed=UINT64_MAX-2;int failed=0;reset(input,2,NULL,0);
    assert(collect(UINT64_MAX,&observed,&failed)==-1 && errno==EOVERFLOW);
    assert(observed==UINT64_MAX-2 && failed && !stored);
    assert(collect(UINT64_MAX,&observed,&failed)==-1 && failed && !stored);
}

static void injected_storage_error(void) {
    const struct read_event input[]={{"ABCD",4,0,4},{"EFGH",4,0,4}};
    uint64_t observed=0;int failed=0;reset(input,2,NULL,0);mode="output_fail";
    assert(collect(8,&observed,&failed)==-1 && observed==4 && failed && !stored);
    mode="normal";
    assert(collect(8,&observed,&failed)==0 && observed==8 && failed && !stored);
}

static void recovered_storage(uint64_t cap) {
    const struct read_event input[]={{"ABCD",4,0,4},{"EFGH",4,0,4}};
    const struct write_event storage[]={{2,0},{-1,EIO}};
    uint64_t observed=0;int failed=0;reset(input,2,storage,2);
    assert(collect(cap,&observed,&failed)==-1);
    assert(observed==4 && failed && stored==2 && !memcmp(output,"AB",2));
    // The same state is reused by the poll loop and final drain. Storage now succeeds.
    assert(collect(cap,&observed,&failed)==(cap<8) && observed==8 && failed);
    assert(stored==2 && stored<=cap && !memcmp(output,"AB",2));
    // Exercise the maintained public encoder/finish consumed by the Lean API.
    run_id=1;run_uid=100000;
    struct result result=result_of(UNKNOWN,9,EPROTO,1);
    result.clean=1;result.triggers=OUTPUT;result.out=observed;
    assert(finish(result)==126 && framed==FRAME_SIZE);
}

int main(void) {
#ifdef LEGACY_CAPTURE
    const struct read_event input[]={{"ABCD",4,0,4},{"EFGH",4,0,4}};
    const struct write_event storage[]={{2,0},{-1,EIO}};
    uint64_t observed=0;int failed=0;reset(input,2,storage,2);
    assert(collect(4,&observed,&failed)==-1 && stored==2);
    assert(collect(4,&observed,&failed)==0);
    fprintf(stderr,"legacy stored=%zu cap=4 observed=%"PRIu64"\n",stored,observed);
    assert(stored<=4);
    return 0;
#endif
    short_transfers();zero_capacity();retry_read();partial_read_fault();overflow();injected_storage_error();
    recovered_storage(4);recovered_storage(8);
    assert(fwrite(frame_output,1,framed,stdout)==FRAME_SIZE);
    return 0;
}
