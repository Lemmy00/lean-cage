/* SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later */
/* §AR-m4-native.semantics: Explicit Linux x86-64 LP64 experiment ABI, not a libc proof. */
typedef unsigned int uint32_t;
typedef unsigned long uint64_t;
typedef unsigned long size_t;
typedef long ssize_t;
extern ssize_t write(int, const void *, size_t);
extern int *__errno_location(void);
#define errno (*__errno_location())
#define EINTR 4
#define EIO 5
extern int strcmp(const char *, const char *);
extern int memcmp(const void *, const void *, size_t);
extern void *memcpy(void *, const void *, size_t);
extern _Noreturn void _exit(int);
_Static_assert(sizeof(int) == 4 && sizeof(long) == 8 && sizeof(void *) == 8, "LP64");
extern ssize_t read(int, void *, size_t);
extern int close(int);
#define EPROTO 71
/* Wait-status macros adapted from glibc bits/waitstatus.h. */
/* Definitions of status bits for `wait' et al.
   Copyright (C) 1992-2024 Free Software Foundation, Inc.
   This file is part of the GNU C Library.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public
   License as published by the Free Software Foundation; either
   version 2.1 of the License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; if not, see
   <https://www.gnu.org/licenses/>.  */

#define WEXITSTATUS(status) (((status) & 0xff00) >> 8)
#define WTERMSIG(status) ((status) & 0x7f)
#define WIFEXITED(status) (WTERMSIG(status) == 0)
#define WIFSIGNALED(status) (((signed char) (((status) & 0x7f) + 1) >> 1) > 0)
