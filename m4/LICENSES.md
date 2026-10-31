Tooling provenance and license review
===================================

This is a research/evaluation experiment, not a production compiler change.
CompCert is by INRIA and AbsInt. Its complete license is retained in the ignored
source checkout at `.tools/m4/CompCert/LICENSE`. The pinned release's noncommercial
license permits research/evaluation; it is not the root Apache license. The listed
semantics/frontend/export files also offer LGPL-2.1-or-later; bundled Flocq and
MenhirLib use LGPL-3-or-later. The whole build is used here only for research.
No CompCert executable or upstream source is committed or redistributed here.
A commercial/production toolchain requires a separate licensing decision.

Review source: https://github.com/AbsInt/CompCert/blob/14d616046360a0b2611ebdfc2f98368af402e1f7/LICENSE

Ubuntu packages are extracted without installation or maintainer scripts.
Coq 8.18.0 (the pre-renaming Rocq release) is LGPL-2.1; its library has additional
notices. OCaml is LGPL-2.1 with linking exception; Findlib is MIT; Zarith is
LGPL-2 with linking exception; Menhir's generator is GPL-2 and its library is
LGPL-2 with linking exception. Exact Ubuntu copyright files for *all* packages
are retained in `.tools/m4/root/usr/share/doc/`, and hashed in the tool report.
These build tools are separate from LeanCage's own source and deployed runtime.
Upstream libraries keep their own notices. Generated Clight data describes
LeanCage's Apache-2.0 C source and imports upstream semantics by name.

The host GCC/preprocessor and libc headers remain explicit frontend dependencies;
their versions, executable/header identities and generated input are recorded.
This does not assert a verified frontend or compiler chain.

The wait-status macro section of `abi.h` is adapted from the recorded host glibc
`bits/waitstatus.h`, copyright 1992-2024 Free Software Foundation, Inc., under
LGPL-2.1-or-later. Its original notice is preserved in that section, and the
license is provided in `m4/LGPL-2.1.txt`. That adapter and its expanded AST retain
their applicable LGPL terms; the root Apache license does not override them.
The maintained helper bodies and original experiment/proof code are Apache-2.0.
