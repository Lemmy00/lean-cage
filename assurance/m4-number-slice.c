// SPDX-License-Identifier: Apache-2.0
// Extracted for the bounded controller source proof; no native workload is executed.
typedef unsigned long uint64_t;
#define UINT64_MAX 18446744073709551615UL
_Static_assert(sizeof(int)==4 && sizeof(long)==8 && sizeof(void*)==8,"LP64");
static int number(const char *text,uint64_t *value)  {
    if(!*text)return -1;
    uint64_t result=0;
    for(const unsigned char *p=(const unsigned char *)text;*p;p++)  {
        if(*p<'0'||*p>'9'||result>(UINT64_MAX-(*p-'0'))/10)return -1;
        result=result*10+(*p-'0');
    }
    *value=result;
    return 0;
}

void(*controller_roots[])(void)={(void(*)(void))number};
