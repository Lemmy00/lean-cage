// SPDX-License-Identifier: Apache-2.0
#define _GNU_SOURCE
#include "process_primitives.h"
#include <fcntl.h>
#include <signal.h>
#include <sys/prctl.h>
#include <sys/ptrace.h>
#include <sys/syscall.h>
#include <unistd.h>

// §AR-entry.effects: Each fixed-arity adapter marshals exactly one Linux/libc operation.
long entry_prctl5(int option,unsigned long a2,unsigned long a3,unsigned long a4,unsigned long a5) {
    return prctl(option,a2,a3,a4,a5);
}
int entry_duplicate_above(int descriptor,int minimum) {
    return fcntl(descriptor,F_DUPFD_CLOEXEC,minimum);
}
long entry_signal_mask(uint64_t mask) {
    return syscall(SYS_rt_sigprocmask,SIG_SETMASK,&mask,NULL,8);
}
long entry_signal_default(int signal) {
    struct { uintptr_t handler,flags,restorer;uint64_t mask; } action={0};
    return syscall(SYS_rt_sigaction,signal,&action,NULL,8);
}
long entry_ptrace4(int request,pid_t child,void *address,void *data) {
    return ptrace((enum __ptrace_request)request,child,address,data);
}
