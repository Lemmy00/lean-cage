Connection proof provenance
===========================

The original connection proofs are Apache-2.0. The three `classical_*` memory
lemmas in `WriteBytes.v` adapt `common/Memory.v` from CompCert commit
`14d616046360a0b2611ebdfc2f98368af402e1f7`; their original attribution and notice
are retained beside the lemmas. They use that file's LGPL-2.1-or-later option.
The license text is retained at `m4/LGPL-2.1.txt`. The root Apache license does not
override these terms. The adaptation derives proof irrelevance from classical
excluded middle rather than introducing CompCert's separate `Axioms.proof_irr`
parameter; it does not change upstream source or the memory definitions.

[Exact upstream source](https://github.com/AbsInt/CompCert/blob/14d616046360a0b2611ebdfc2f98368af402e1f7/common/Memory.v).
The existing research-tool license review in `m4/LICENSES.md` remains applicable;
no compiled compiler, runtime or upstream source tree is redistributed here.
