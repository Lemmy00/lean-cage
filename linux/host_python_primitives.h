// SPDX-License-Identifier: Apache-2.0
// §AR-host-boundary.primitives: Give the single fcntl operation a fixed native ABI.
#ifndef LEANCAGE_HOST_PYTHON_PRIMITIVES_H
#define LEANCAGE_HOST_PYTHON_PRIMITIVES_H

int leancage_host_fcntl(int descriptor, int command, int argument);

#endif
