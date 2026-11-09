// SPDX-License-Identifier: Apache-2.0
// §AR-entry.caller: Fresh image before any Lean runtime is initialized in the entry child.
#include "entry_decimal.h"
extern int entry_descriptor_flags(int fd,int flags);

static _Noreturn void guest(int input,int output,int errors,int failure) {
#ifndef LEANCAGE_ENTRY_TEST
    if(strcmp(mode,"normal"))fail_child(failure,1,EINVAL);
#endif
    int handles[]={input,output,errors,failure};
    char uid[32],numbers[4][32];uint64_t encoded;
    if(run_uid<100000||run_uid>100999)fail_child(failure,1,EINVAL);
    int count=entry_decimal(uid,run_uid);
    if(count<=0||(size_t)count>=sizeof(uid))fail_child(failure,1,count<0?error_number():EOVERFLOW);
    if(number(uid,&encoded)||encoded!=run_uid)fail_child(failure,1,EPROTO);
    for(unsigned i=0;i<4;i++) {
        if(handles[i]<4)fail_child(failure,3,EBADF);
        for(unsigned j=0;j<i;j++)if(handles[i]==handles[j])fail_child(failure,3,EBADF);
        count=entry_decimal(numbers[i],(uint64_t)handles[i]);
        if(count<=0||(size_t)count>=sizeof(numbers[i]))fail_child(failure,1,count<0?error_number():EOVERFLOW);
        if(number(numbers[i],&encoded)||encoded!=(uint64_t)handles[i])fail_child(failure,1,EPROTO);
        if(entry_descriptor_flags(handles[i],0))fail_child(failure,3,error_number());
    }
    if(entry_descriptor_flags(STDOUT_FILENO,FD_CLOEXEC))fail_child(failure,3,error_number());
    char *args[74];
    args[0]="/leancage-entry";
#ifdef LEANCAGE_ENTRY_TEST
    if(strcmp(mode,"normal"))args[0]="/leancage-entry-test";
#endif
    args[1]=preflight?"check":"run";args[2]=uid;
    args[3]=root_path;
    for(unsigned i=0;i<4;i++)args[4+i]=numbers[i];
    args[8]=(char *)mode;
    size_t i=0;while(policy.args[i]&&i<64){args[9+i]=policy.args[i];i++;}
    if(policy.args[i])fail_child(failure,1,E2BIG);
    args[9+i]=NULL;
    char *const env[]={"LC_ALL=C",NULL};
    execve(args[0],args,env);
    fail_child(failure,1,error_number());
}
