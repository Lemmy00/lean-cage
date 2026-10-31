/* SPDX-License-Identifier: Apache-2.0 */
/* §AR-m4-native.semantics: Passive ABI/macro check, no OS enforcement operations. */
#include <sys/types.h>
#include <sys/wait.h>
#include <stdint.h>
#include <errno.h>
#include <stddef.h>
static int actual_exited(int s) { return WIFEXITED(s); }
static int actual_signalled(int s) { return WIFSIGNALED(s); }
static int actual_status(int s) { return WEXITSTATUS(s); }
static int actual_signal(int s) { return WTERMSIG(s); }
_Static_assert(EINTR == 4 && EIO == 5 && EPROTO == 71, "Linux errno ABI");
#undef WIFEXITED
#undef WIFSIGNALED
#undef WEXITSTATUS
#undef WTERMSIG
#undef errno
#include "abi.h"
_Static_assert(sizeof(uint32_t) == 4 && sizeof(uint64_t) == 8, "Integer ABI");
_Static_assert(sizeof(size_t) == 8 && sizeof(ssize_t) == 8, "Transfer ABI");
int main(void) {
    for (int s = 0; s <= 65535; s++) {
        if (actual_exited(s) != WIFEXITED(s) || actual_signalled(s) != WIFSIGNALED(s)
            || actual_status(s) != WEXITSTATUS(s) || actual_signal(s) != WTERMSIG(s))
            return 1;
    }
    return 0;
}
