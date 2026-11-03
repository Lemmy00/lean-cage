# Independent review of the repaired parent composition

Review input: `b96168507c2574402b23ce4cdb382ab6fa437808`. The independent reviewer
accepted all six bounded-package requirements in `M4-CONTINUE.md`, conditional
only on a successful corrected `./scripts/check_m4_all.sh` replay. The current
outcome is recorded in `assurance/m4-parent-validation.json`; this review alone
does not establish that aggregate outcome. Apply [§AR-m4-parent.audit](../architecture/AR-m4-parent.md#audit-maintained-evidence-and-preserved-candidate) and
[§REQ-proof-integrity.statement](../requirements/REQ-proof-integrity.md#statement-review-the-proposition).

The previous review rejected `d1f361e` for missing accepted-frontier elimination
and two compiled declaration-inventory bypasses. Both are closed:
`trace_post_bounds_cut` excludes the unfinished alternative at actual acceptance,
`residual_acceptance_history` establishes matching signed history there, and
the composed numeric interface exports `frontier_guarantee`. No input premise
or machine transition was removed. The cut's dependence on current external-call
scope is explicit and must be revalidated when that scope changes.

Compiled module signatures now determine the inventory, including local and
generated constants. Both review counterexamples are compiled regression inputs.
Input representation remains tied to the execution's starting memory; the 67
allocated cases preserve exact rejection ordering, retained stores and loss at
every prefix. Independently constructed source bounds exclude waits and imply
neither time bounds nor unconditional termination.

Independent canonical replay of `python3 m4/parent/check.py` passed in 175.506
seconds: 300 Rocq records, two Lean theorem records, 51 exact artifacts and 31
passing regressions. The unchanged C control passed; all three actual guard,
cast and comparison mutations were rejected. Eight compiler-interface records
reproduced. The separate receipt gate and its 22 regressions passed.

All 221 earlier type/foundation rows match. Original preservation remains 113
identical records and eight explicitly amended/removed interfaces. Original
snapshots, native source, maintained pins and the sixteen-entry ledger remain
unchanged. The rejected-review evidence copies match `d1f361e` byte for byte.

The independent focused output SHA-256 is
`fac89bdda090b42ec071050f5d63bfb75dd2f8afe8b7e2662912d3739a5e84c2`, matching the
author's focused output. Its compressed copy and the frozen corrected review
inputs are identified in `assurance/m4-parent-promotion.json`. Subsequent
navigation amendments must preserve all 300 reviewed type/foundation records
and 51 proof artifacts.

This accepts only the stated local source contract after its aggregate gate.
Ordinary Lean security connection, Linux effects, compiler/runtime/loader
composition and all sixteen original obligations remain open. No fresh VM
workload was run. Hardware-channel confidentiality remains M5.
