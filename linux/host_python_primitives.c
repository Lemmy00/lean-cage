// SPDX-License-Identifier: Apache-2.0
// §AR-host-boundary.primitives: This adapter forwards one Linux operation and its arguments.
#define _GNU_SOURCE
#include <fcntl.h>
#include "host_python_primitives.h"

int leancage_host_fcntl(int descriptor, int command, int argument) {
    return fcntl(descriptor, command, argument);
}
