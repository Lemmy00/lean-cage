# Independent M4 checkpoint review — 2026-11-01

Review input: `80d4bbe5db1e0d1cc75f250df0fa32baa7738d04` on `main`, with a clean
working tree. The author paused at that checkpoint. Accepted local claims remain
those through initialization commit `2db87b46d861ffd1c10e295a985818197b8c6170`.
The [checkpoint handoff](M4-checkpoint-handoff.md) and all original evidence are
preserved. This review applies [§REQ-proof-integrity.statement](../requirements/REQ-proof-integrity.md#statement-review-the-proposition),
[§REQ-proof-integrity.provenance](../requirements/REQ-proof-integrity.md#provenance-preserve-evidence-and-scope) and [§AR-m4-controller.composition](../architecture/AR-m4-controller.md#composition-remaining-controller-obligations).

**Decision:** retain the parent/numeric/initialization work as a review candidate.
The inspected universal contracts do not assume successful numeric parsing or
parent admission, and no concrete unsound proof was identified. The public
composition interface and acceptance evidence need the corrections below before
promotion. This is a bounded source/statement/evidence review, not an independent
certification of all prior M4 proofs or a Linux/executable security review.

The current continuation assignment is [M4-CONTINUE.md](../../M4-CONTINUE.md).
It preserves the original full-M4 destination and gives the next agent concrete
acceptance requirements, later dependencies and an original-obligation map.

## Findings that prevent candidate promotion

### 1. Link parent admission to the actual composed history

`m4/parent-checkpoint/ParentInitialization.v`, definition
`parent_initialization_frontier`, retains an existential admitted state without
relating that state to the execution history under consideration. The parent
endpoint itself carries an observation, but composition drops the endpoint.
For valid parsed values, an admitted endpoint can be constructed independently
of the particular execution. The separate matching theorems construct a source
path internally but do not export its parent-event decomposition.

This is an acknowledged statement-strength gap, not evidence that the source
comparison is wrong. Require a universal prefix-history result: accepted
initialization follows the actual matching parent observation; preceding
failures make no observation; mismatch preserves the differing observation.
Limit this to the selected region. The arbitrary continuation after its endpoint
must not inherit a persistent parent-identity or liveness claim.

### 2. Export the initial input representation

`ValidationMatching.v`'s `allocated_validation_matching` returns a source run,
initial memory and prospective stores, but does not expose the relation between
that initial memory/argv and the supplied numeric, parent, export, digest and
guest byte lists. Its proof constructs those ownership/table facts and then
hides them. `NumericWitnesses.v` exposes a byte-list equality without its input
memory/table relation. `ValidationAllocation.v` already constructs the missing
storage facts.

Export a shared representation bundle alongside each allocated run. This should
make the results reusable without reconstructing hidden proof choices. It must
not pretend that allocated logical inputs establish physical process argv
provenance, or add unnecessary separation restrictions to universal contracts.

### 3. Complete the composed cases and negative controls

The 24 parent cases start at the parent suffix. The allocated matching theorem
assumes successful numeric parsing and a matching positive parent to exhibit a
path. Those results do not replace the complete numeric-to-initialization case
table. Require useful acceptance, early/late numeric failure, parent validation
and mismatch, later rejection ordering, and interruption at meaningful memory
and observation boundaries. Check retained earlier stores explicitly.

Add compiled mutations of actual guards/comparison and checks for fabricated
history or erased input representation. Preserve unchanged positive controls.
The earlier checkpoints' negative tests do not test this new candidate.

### 4. Harden the inventory before extending it

The inherited Rocq `proof_names` helper in `m4/main/check.py` finds declarations
by regular expression. Unlike the Lean audit, it does not derive the whole
inventory from the checked environment. Qualified/attributed commands or
proof-valued definitions can fall outside that recognized syntax. The currently
reviewed candidate uses the supported theorem forms; this finding does not show
that a current security proof escaped checking. Before expansion, enumerate the
actual proof environment or explicitly reject unsupported forms and add negative
inventory tests. A source-file hash does not make an incomplete claim inventory
complete.

## Evidence correction made by this review

The frozen candidate checker compares proof/source/artifact fields but does not
validate `assurance/m4-parent-checkpoint-validation.json` and its six archived
receipt hashes. Thus receipt metadata or a log could change without that checker
noticing. The inspected checkpoint files were consistent; this was a protection
gap, not a discovered bad receipt or failed proof.

An additive validator and tamper tests under `m4/review/` check that archival
boundary without modifying the candidate or its snapshot. The new aggregate
`scripts/check_m4_all.sh` makes the full implemented dependency replay explicit,
including the candidate and receipt checks. Passing it does not accept the
candidate or close any correspondence obligation.

## What the inspected contracts do preserve

- `ParentRegion.v` requires ordinary non-loss progress and quantifies over every
  transition of the extended local machine; its certificate is proved internally.
- `ParentLift.v` handles the newly added transitions by excluding an unsupported
  `getppid` boundary from an earlier certificate that already promises progress.
- Numeric incompleteness remains a branch of the general contract. Success and
  matching-parent assumptions belong to separately named constructive witnesses.
- Arbitrary signed parent observations, waiting and terminal loss remain present.
- Memory frames retain executed earlier writes. Prospective later-store witnesses
  do not mean those stores happened on an earlier rejecting path.
- The bound measures non-wait steps. It is not a wall-clock bound or unconditional
  termination result. A rejection endpoint at `result_of` is not completed
  reporting, cleanup or process exit.

The candidate archive inventories 121 Rocq declarations and two Lean theorems,
not 123 independent security guarantees. The inspected public source contracts
retain the documented classical/extensionality and CompCert external-semantics
foundations. Lean records retain `propext`, `Classical.choice`, and `Quot.sound`.
Imported computational records expose their separate definitional-UIP model.

## Changes to the continuation strategy

Proceed from local validation to explicit whole-controller state/effect
composition. Pull two feasibility edges forward alongside that work:

1. Under [§AR-m4-bridge.import](../architecture/AR-m4-bridge.md#import-checked-terms-and-explicit-logical-model), check semantic faithfulness between the original
   Lean computation and imported representation, and establish the route back
   to the ordinary Lean security theorem required by [§REQ-proof-integrity.kernel](../requirements/REQ-proof-integrity.md#kernel-kernel-checked-evidence).
2. Relate the custom byte-aware/loss transitions to the semantics required by the
   actual compiler theorem. The local machine replaces stock external/builtin
   steps; recompiling its proofs does not transfer stock compiler correctness.

Start a source-connected pinned-Linux effect path early as well. Its contract
must include real descriptor/byte provenance, interference and errors. A syscall
table or VM success is not a proof of the kernel connection. Each new package
must identify which original obligation and composition edge it advances.

All sixteen entries in `assurance/m4-obligations.json` remain open. M4.4–M4.6,
physical argv provenance, later setup/supervision/cleanup, real Linux effects,
compiler/runtime/loader correspondence and hardware confidentiality have not
been established by this review.

## Navigation and frozen evidence

README, AGENTS, the development guide and `RM-roadmap.m4.entry` still route new
work to concluded M4.1 feasibility. The roadmap introduction and some assurance
and architecture-index summaries lag the accepted local results. These files
are transitively bound into the exact frozen candidate snapshot. Changing them
during this review would change the input being independently reproduced.

The root continuation document supplies current navigation additively. Promotion
must include a reviewed navigation/evidence amendment, retain the old feasibility
contract and frozen candidate, and add a current `RM-roadmap.m4.next` entry.
Never regenerate historical proof expectations just to make documentation edits
pass. The recorded handoff and continuation explain how to replay the old input
and the amended maintained package separately.

## Validation

All twelve dependency-replay commands completed with exit code zero against the
reviewed input. The sequence was foundation, connection (including M4.1), bridge,
controller, plan, main, policy, arguments, digest, validation, initialization and
the frozen parent candidate. This is a fresh replay, not a restatement of the
author's six checkpoint receipts.

| Check | Fresh result |
|---|---|
| Foundation | M1–M3 proof/audit/build checks and 74 Python tests passed; archived VM evidence validated. |
| Reporting/source connection | 1,113 Rocq and 103 Lean theorem records checked, including independent kernel replay and 37 evidence regressions. |
| Strict bridge | 135 Rocq and 33 Lean theorem records checked; translated terms and independent kernel replay passed. Translation faithfulness remains open. |
| Controller through initialization | All eight maintained package gates passed, preserving their reviewed statements, foundations and dependency/artifact identities. |
| Frozen parent candidate | 121 Rocq records, two Lean theorems and all 36 compiled artifacts matched the snapshot. Independent kernel checking passed. This does not promote the candidate. |
| New receipt protection | Six original archived receipts verified; all 22 new tamper regressions passed. |
| Remaining checks | M3 compiled-artifact identities, full Grund consistency/format checks, aggregate shell syntax and staged whitespace checks passed. |

The [validation receipt](../../assurance/m4-independent-review-validation.json)
records exact commands, exit codes, elapsed times and log hashes. Raw outputs are
preserved in `assurance/m4-independent-review-logs.json.gz`. Counts above overlap
through dependencies and must not be added into a security score.

Every previously tracked file remains unchanged: proofs, native sources, pins,
accepted manifests, the candidate snapshot and original obligation ledger.
Only review/continuation documents, additive receipt checking, the aggregate
entrypoint and this review's evidence are added. No fresh VM workload was run;
the distinction between archived VM validation and actual replay is retained.
