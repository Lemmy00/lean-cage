// SPDX-License-Identifier: Apache-2.0
// §AR-entry.effects: One bounded formatting call; caller readback establishes numeric agreement.
#include <inttypes.h>
#include <stdio.h>
#include "entry_decimal.h"

int entry_decimal(char output[32],uint64_t value) {
    return snprintf(output,32,"%" PRIu64,value);
}
