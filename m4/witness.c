/* SPDX-License-Identifier: Apache-2.0 */
/* §AR-m4-native.evidence: In-memory scripted effects; no helper/guest OS operations. */
#include <setjmp.h>
#define read m4_read
#define close m4_close
#define write m4_write
#define __errno_location m4_errno_location
#define _exit m4_exit
#include "slice.c"
#undef read
#undef close
#undef write
#undef __errno_location
#undef _exit

static jmp_buf escape;
static int scripted_errno, script[512], errors[512], script_size, script_pos;
static unsigned char observed[2048];
static size_t observed_size;
static unsigned char read_data[256];
static size_t read_size, read_pos;
int *m4_errno_location(void) { return &scripted_errno; }
ssize_t m4_write(int fd, const void *data, size_t count) {
    (void)fd;
    int n = script_pos < script_size ? script[script_pos] : (int)count;
    scripted_errno = script_pos < script_size ? errors[script_pos] : 0;
    script_pos++;
    if (n == -2) longjmp(escape, 2); /* Environment process-loss witness. */
    if (n > 0) {
        if ((size_t)n > count || observed_size + (size_t)n > sizeof(observed))
            longjmp(escape, 3); /* Reject an inadmissible transfer contract. */
        memcpy(observed + observed_size, data, (size_t)n);
        observed_size += (size_t)n;
    }
    return n;
}
ssize_t m4_read(int fd, void *data, size_t count) {
    (void)fd;
    int n = script_pos < script_size ? script[script_pos] : 0;
    scripted_errno = script_pos < script_size ? errors[script_pos] : 0;
    script_pos++;
    if (n == -2) longjmp(escape, 2);
    if (n > 0) {
        if ((size_t)n > count || read_pos + (size_t)n > read_size)
            longjmp(escape, 3);
        memcpy(data, read_data + read_pos, (size_t)n);
        read_pos += (size_t)n;
    }
    return n;
}
int m4_close(int fd) { (void)fd; return 0; }
_Noreturn void m4_exit(int status) { longjmp(escape, 1000 + status); }
void witness_reset(const char *fault_mode, unsigned long run, unsigned uid, int check) {
    mode = fault_mode;
    run_id = run;
    run_uid = uid;
    preflight = check;
    observed_size = 0;
    script_size = 0;
    script_pos = 0;
    scripted_errno = 0;
    read_size = read_pos = 0;
}
void witness_effect(int n, int error) {
    if (script_size < 512) {
        script[script_size] = n;
        errors[script_size++] = error;
    }
}
unsigned long witness_output(unsigned char *p) {
    memcpy(p, observed, observed_size);
    return observed_size;
}
int witness_write(const unsigned char *p, unsigned long n) {
    int escaped = setjmp(escape);
    return escaped ? 10000 + escaped : write_all(3, p, n);
}
int witness_decode(const unsigned char *p, unsigned long sequence) {
    struct result r;
    return decode_frame(p, sequence, &r);
}
int witness_send(unsigned kind, unsigned stage, unsigned detail, unsigned entry) {
    struct result r = result_of(kind, stage, detail, entry);
    r.elapsed = 1;
    int escaped = setjmp(escape);
    return escaped ? 10000 + escaped : send_frame(3, 0, r);
}
int witness_failure(unsigned stage, int error) {
    int escaped = setjmp(escape);
    if (escaped) return escaped;
    fail_child(3, stage, error);
}
int witness_finish(unsigned kind, unsigned detail) {
    struct result r = result_of(kind, 0, detail, 1);
    int escaped = setjmp(escape);
    return escaped ? 10000 + escaped : finish(r);
}
unsigned witness_errno(int n) { scripted_errno = n; return (unsigned)error_number(); }
unsigned witness_get32(const unsigned char *p) { return get32(p); }
unsigned long witness_get64(const unsigned char *p) { return get64(p); }
void witness_put32(unsigned char *p, unsigned x) { put32(p, x); }
void witness_put64(unsigned char *p, unsigned long x) { put64(p, x); }

int witness_receive(const unsigned char *data, unsigned long length,
                    int bad, int entered, int leader_done, int leader_status) {
    if (length > sizeof(read_data)) return -99;
    memcpy(read_data, data, length);
    read_size = length;
    read_pos = 0;
    int escaped = setjmp(escape);
    if (escaped) return 10000 + escaped;
    struct result r = m4_collect_failure(3, bad, entered, leader_done, leader_status);
    return (int)(r.kind * 10000000 + r.stage * 100000 + r.detail * 10 + r.entry);
}
