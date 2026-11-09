// SPDX-License-Identifier: Apache-2.0
// §AR-entry.caller: Fixed ABI for one bounded libc formatting operation.
#ifndef LEANCAGE_ENTRY_DECIMAL_H
#define LEANCAGE_ENTRY_DECIMAL_H
#include <stdint.h>

int entry_decimal(char output[32],uint64_t value);
#endif
