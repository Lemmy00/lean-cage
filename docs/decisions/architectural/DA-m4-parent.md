# DA-m4-parent: Preserve the candidate and track observations in composition

The continuation under [§AR-m4-parent.history](../../architecture/AR-m4-parent.md#history-selected-execution-history) implements the input-validation
portion of [§FS-workspace.policy](../../functional-spec/FS-workspace.md#policy-bounded-typed-request). The frozen candidate's state-only existential
admission does not identify the parent event in a particular composed execution.
Use a history-indexed source certificate whose continuations carry the actual
observations accumulated by transitions. Lift earlier string and numeric regions
without introducing observations, and preserve the observation through later
initialization. This is a supplemental trace contract, not a persistent identity
claim.

Eliminate a residual certificate at the actual post-bounds control state by a
source-specific cut theorem. Its fixed internal continuation reaches the next
out-of-slice `getenv` call, which has no ordinary local-machine progress; none of
those intervening states is a selected endpoint. This is an explicit dependency
on the current effect scope, not a Linux interpretation of `getenv`. Preserve
arbitrary execution after the selected completed prefix.

Keep the candidate source/snapshot unchanged. Put maintained proofs and evidence
under `m4/parent/` and `assurance/m4-parent-*`. Export allocation ownership facts
alongside runs. Enumerate compiled module signatures as the maintained inventory
authority, including generated and local constants. Retain source restrictions
as a separate conservative check and reject unsupported signature syntax.

This decision does not accept the package before its cases, full statement review
and maintained gate pass. It leaves the original correspondence ledger open.
