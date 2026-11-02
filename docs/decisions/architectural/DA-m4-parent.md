# DA-m4-parent: Preserve the candidate and track observations in composition

The continuation under [§AR-m4-parent.history](../../architecture/AR-m4-parent.md#history-selected-execution-history) implements the input-validation
portion of [§FS-workspace.policy](../../functional-spec/FS-workspace.md#policy-bounded-typed-request). The frozen candidate's state-only existential
admission does not identify the parent event in a particular composed execution.
Use a history-indexed source certificate whose continuations carry the actual
observations accumulated by transitions. Lift earlier string and numeric regions
without introducing observations, and preserve the observation through later
initialization. This is a supplemental trace contract, not a persistent identity
claim.

Keep the candidate source/snapshot unchanged. Put maintained proofs and evidence
under `m4/parent/` and `assurance/m4-parent-*`. Export allocation ownership facts
alongside runs. Reject unsupported Rocq declaration syntax in the maintained
inventory until checked-environment enumeration replaces the restriction.

This decision does not accept the package before its cases, full statement review
and maintained gate pass. It leaves the original correspondence ledger open.
