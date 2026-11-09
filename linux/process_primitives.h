// SPDX-License-Identifier: Apache-2.0
#ifndef LEANCAGE_PROCESS_PRIMITIVES_H
#define LEANCAGE_PROCESS_PRIMITIVES_H
#include <stdint.h>
#include <sys/types.h>

// §AR-entry.caller: Fixed-arity ABI for one native operation per call.
long entry_prctl5(int option,unsigned long a2,unsigned long a3,unsigned long a4,unsigned long a5);
int entry_duplicate_above(int descriptor,int minimum);
long entry_signal_mask(uint64_t mask);
long entry_signal_default(int signal);
long entry_ptrace4(int request,pid_t child,void *address,void *data);

#endif
