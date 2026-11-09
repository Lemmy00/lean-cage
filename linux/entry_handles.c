// SPDX-License-Identifier: Apache-2.0
// §AR-entry.effects: One nonvariadic descriptor-flag operation; no setup sequencing.
#include <fcntl.h>

int entry_descriptor_flags(int fd,int flags) {
    return fcntl(fd,F_SETFD,flags);
}
