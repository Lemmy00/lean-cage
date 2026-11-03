LeanCage's original scripts and proof modules use Apache-2.0, except for adapted
upstream compiler proofs. This package is a research/evaluation experiment under
the toolchain provenance recorded in `m4/LICENSES.md` and the pinned locks.

`VerifiedBackend.v` adapts CompCert's `driver/Compiler.v` and retains its INRIA
copyright and Non-Commercial License Agreement notice. That upstream license
applies to the adapted file; the repository's Apache license does not replace it.
`allocation.py` generates a derivative of `backend/Allocproof.v`, with the
original notice and all validator/correctness conditions preserved. Generated
compiler source and candidate-tool copies retain upstream notices and the
licenses of their corresponding source files. The complete CompCert license
remains in `.tools/m4/CompCert/LICENSE` and the original pinned source checkout.
The applicable INRIA agreement is reproduced verbatim in
`INRIA-NON-COMMERCIAL.txt` alongside the adapted proof.

No compiler executable, candidate assembly text or deployed helper binary is
redistributed by this package. Existing tool/runtime notices and the ABI header's
LGPL obligations recorded in `m4/LICENSES.md` remain applicable.
