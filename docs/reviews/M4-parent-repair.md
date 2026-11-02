# M4 parent composition repair — author handoff

**Status: repaired package candidate; independent promotion review pending.**
The accepted local baseline remains initialization commit `2db87b4`. The frozen
`80d4bbe` candidate and its initialization snapshot are preserved. This package
addresses the first assignment in [M4-CONTINUE.md](../../M4-CONTINUE.md) under
[§AR-m4-parent.history](../architecture/AR-m4-parent.md#history-selected-execution-history), [§AR-m4-parent.inputs](../architecture/AR-m4-parent.md#inputs-owned-input-representation) and [§REQ-proof-integrity.statement](../requirements/REQ-proof-integrity.md#statement-review-the-proposition).
It does not close any of the sixteen original correspondence obligations.

The local producer is owned numeric, parent and argument memory at the actual
numeric-initialization block. The consumers are the existing initialization,
argument-length and policy-bound certificates at their unchanged continuations.
The relevant original ledger edges are `M4-controller`, `M4-supervisor` and
`M4-m3-policy`. Physical process entry/argv and later setup remain unconnected.

## Statements to review

`TraceRegion.trace_certificate` indexes every live continuation by the parent
observations accumulated by its actual transitions. `TraceExecution` splits each
execution into an unfinished prefix or a selected completed prefix and arbitrary
later continuation. The completed prefix's result receives `observations prefix`;
it cannot substitute an independently chosen admitted state or event list.

`ParentTrace` preserves empty histories through guard failures and records the
actual signed observation through mismatch or admission. `TraceInitialization`
retains that history through later checks and writes. `NumericTrace` constructs
the whole selected-region certificate without assuming numeric success, parent
admission or later policy validity. Its numeric-rejection branch has an empty
observation history and the exact first numeric reporting endpoint.

`InputRepresentation.validation_input_representation` returns the allocated
strings and argument-table ownership in the starting memory of the same run,
all supplied byte equalities and numeric mappings. Both allocated public
interfaces export it. The separately named matching interface also exports
exactly one actual observation. The universal premises retain permitted aliases;
fresh allocated witnesses have stronger separation. No physical argv provenance
or persistent parent identity follows.

`CompositionExecution.allocated_composition_execution` permits any selected
signed observation and retains numeric/parent failures. Its endpoint gives exact
prospective stores and the actual first rejection or post-bounds continuation.
`CompositionSamples` checks 67 complete-composition rows, with explicit first
decisions and retained numeric store vectors. They include useful acceptance,
early/late numeric failures, invalid/zero/overflow/out-of-range parents,
mismatches, and export/digest/executable/argument/bounds ordering. Earlier parser
and initialization examples remain preserved.

`CompositionWitnesses.composition_samples_source` exports actual allocated
executions for every row and loss after every prefix with precisely that prefix's
memory. Thus interruption is available on both sides of each executed write and
observation, including loss immediately and at the final selected boundary.
`CompositionLoss.actual_observation_loss_boundaries` additionally identifies the
actual call/return and shared memory before/after an observation. This is loss at
source boundaries, not deployed machine-store atomicity. Arbitrary library and
parent waits remain; step bounds exclude waits and imply no elapsed-time bound
or unconditional termination.

## Inventory, controls and preservation

The maintained inventory accepts a restricted vernacular and rejects unsupported
qualified/attributed/scoped declarations explicitly. It audits every supported
named `Definition` and `Fixpoint` as well as theorem forms. Proof-valued
definitions therefore enter the full type/foundation comparison. Nested and
proof-mode definitions are unsupported. The frozen candidate's original checker
and narrow supported source forms are preserved.

Native controls run the pinned frontend on unchanged C and three real edits to
the parent guard, cast and comparison. A kernel-checked whole-main identity is
the positive control and rejects the changed translations. These are source
binding controls; they are not deployed binary correspondence proofs. Integrity
regressions cover missing/changed statements, foundations, exports, artifacts,
fabricated history, erased representation, receipts and navigation amendments.

The preservation gate compares every original candidate theorem. It permits
exactly eight documented interface amendments/removal and requires unchanged
transitive foundations for each revised declaration. All other 113 original
statement/foundation records are identical. State-only compatibility lemmas stay
available; the trace contracts are the new public composition interface.
`parent_getppid` is removed, the unused export contract parameter is removed,
and the allocated decision bound uses independently constructed source lengths
instead of choosing its own trace cost.

The navigation amendment enumerates seven documents and 27 dependent metadata
records. Its validator compares original and amended JSON and permits only
enumerated document/dependency hashes; theorem, assumption, export and compiled
artifact fields cannot change. The exact pre-amendment aggregate replay is
archived separately. The additive frozen-candidate replay rebuilds its unchanged
proofs against the same compiled dependencies and compares every original type,
foundation, export and artifact, allowing only the enumerated navigation hashes.
Neither the frozen verifier nor its snapshot is refreshed.

The initial repaired-package collection used isolated build directories. Rocq
embeds physical source paths in compiled objects, so those artifact identities
differ from the maintained build location even with identical proof sources,
full propositions and foundations. The initial build records are retained in
`assurance/m4-parent-initial-build-output.json.gz` and
`assurance/m4-compiler-initial-build-output.json.gz`; the explicit build-root
record documents this change. Maintained expectations bind the canonical build
locations and still compare exact compiled hashes. This changes no original
candidate or initialization snapshot. The focused receipt gate additionally
requires its exact inventory; an empty list cannot disable receipt checking.

## Replay and residual edges

Full inventories and raw output are recorded separately in the parent claim,
evidence and proof-output records. The maintained replay is:

```sh
./scripts/check_m4_all.sh
```

The focused command is `python3 m4/parent/check.py`; it requires the preceding
chain to have been built. `--collect` writes an ignored report for review and
never changes expectations. Validation receipts distinguish exact baseline
replay, amended-chain replay and focused checking. No fresh VM workload is run.

The foundations remain the previously reviewed CompCert external-semantics
parameters and classical/extensionality foundations. Imported computation keeps
its separately identified definitional-UIP model; the two ordinary Lean plan
theorems retain their prior axioms. Full records, including definitions, must be
reviewed rather than treating the declaration inventory as a security score.

This is local Rocq source evidence plus separate Lean representation lemmas.
The ordinary Lean security-proof connection required by [§REQ-proof-integrity.kernel](../requirements/REQ-proof-integrity.md#kernel-kernel-checked-evidence)
is still open, as are translation faithfulness, physical argv, persistent process
identity, libc/Linux effects and interference, compiler-semantics compatibility,
native/Lean runtime, linking/loader and composed profile review. M4.4–M4.6 and
full M4 remain incomplete. Hardware confidentiality remains M5.
