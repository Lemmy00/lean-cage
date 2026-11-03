# M4 checkpoint and verification handoff

The user requested a break at the next checkpoint and a handoff for independent
verification. Work is paused after preserving the current parent/numeric
composition candidate. The accepted milestone claims remain those at
initialization commit `2db87b46d861ffd1c10e295a985818197b8c6170`.
This handoff applies [§REQ-proof-integrity.statement](../requirements/REQ-proof-integrity.md#statement-review-the-proposition) and
[§AR-m4-controller.composition](../architecture/AR-m4-controller.md#composition-remaining-controller-obligations); it does not close an obligation.

## Current milestone position

| Package | State at this checkpoint |
|---|---|
| M1–M3 | Accepted for their documented conditional profiles and VM evidence. |
| M4.1 | Bounded native-semantics feasibility result recorded; original direct effect adapter rejected. |
| M4.2 | Substantial source-connected reporting, framing and imported computation results; translation faithfulness and full composition remain open. |
| M4.3 | Active controller work through numeric parsing, policy bounds, arguments, digests, caller string checks and sequential initialization. Parent/numeric composition is the candidate preserved here. |
| M4.4–M4.6 | Pinned Linux, executable/runtime chain and independent composed profile review remain open. |
| M5 | Hardware-channel confidentiality remains later work. |

All sixteen entries in `assurance/m4-obligations.json` remain open. The milestone
map is [§RM-roadmap.m4.packages](../roadmap.md#m4packages-integrated-product-deliveries). No proof count is a completion percentage.

## Accepted work to verify first

The latest accepted commit adds actual flag/pointer stores and continuous
export-to-policy-bounds validation. It proves ordered memory changes and exact
first rejection within that source region, retaining arbitrary library waits and
process loss. Mode/preflight remains a separate region. The inventory contains
81 Rocq theorem records, two Lean theorem records, three imported computational
records and twenty artifacts. Forty-five allocated source cases include nine
acceptances and thirty-six rejections. Four configuration memory stages have
allocated process-loss witnesses. Twelve gate regressions and three compiled
negative controls protect the evidence boundary.

Its sixteen recorded validation receipts cover the repository, artifacts,
original source connection, bridge, decimal controller, plan, main numeric block,
policy, arguments, digests, caller validation, initialization collection and
maintained checking, formatting, integrity and diff. CI run `41281764829` passed
for that exact commit; the CI workflow is the foundation check and does not
replace the local M4 chain. Complete scope and assumptions are in
[the initialization review](M4-initialization.md), with full statements in
`assurance/m4-initialization-claims.json` and archived raw output in
`assurance/m4-initialization-proof-output.json.gz`.

The preceding accepted checkpoints, newest first, are:

| Commit | Bounded result |
|---|---|
| `572df1e49c1009e5057c2f63cf5c308bfe0923a5` | Actual caller-string checks and live plan agreement. |
| `7f94dcaa517a6609144c99f4c94a7f2cd4d1083e` | Complete digest recognizer and live parser byte agreement. |
| `90461f618929b6734bec22c6c43fbe47ee687b0b` | Guest argument-length accumulation and subsequent bounds. |
| `a6f236ff9981b6306ff49f8168d9d9e1550f81ef` | Actual policy-bound guards and imported live policy agreement. |
| `65dba9c9fc2641b8ff1b80314e2bf614cd994d70` | Complete-helper numeric initialization and parser loop. |
| `80a192b25485c3b0839203b7e044b7b5f3a9dca7` | Live launch-plan layout, numeric bytes and imported parser. |
| `c93c550ec9c0559e1421e624cd637ff570f44b73` | Native unsigned-decimal parser source connection. |
| `dfaf997d040bd7b8bccb76087d3839bbc3086ec9` | Imported frame operations and source publication composition. |

## Preserved candidate

The source is in `m4/parent-checkpoint/`: thirty-five Rocq modules and
`Parent.lean`. The original experiment remains under ignored
`.tools/m4/parent-experiment/`. `provenance.json` records the original source
hashes; promotion into this review directory adds only license/scope comments.
The [candidate contract and replay instructions](../../m4/parent-checkpoint/README.md)
are explicit about the pending review. No accepted manifest, native helper,
toolchain pin or original obligation is changed by this checkpoint.

The main reading order is:

1. `ParentMachine.v`, `ParentRegion.v`, `ParentLift.v`: arbitrary signed `getppid`
   observations, waits/loss, and preservation of earlier certificates under the
   extended machine. Review the quantification over all new transitions.
2. `ParentSource.v`, `ParentDecision.v`, `ParentRuns.v`: real argv[12] parsing,
   short-circuit guards, checked narrowing, actual comparison and exact rejection
   call. Successful admission means a positive value at most `INT_MAX` matches
   the signed observation. It does not mean the process remains the parent.
3. `ParentInitialization.v`, `NumericComposition.v`: continuous selected source
   regions, exact early failures and partial stores. The public general contracts
   construct certificates internally and do not assume numeric or parent success.
4. `NumericWitnesses.v`, `ValidationMatching.v`: inhabited shared input/storage
   premises and a separate actual matching run through initialization. The latter
   deliberately assumes ten successful parses and a matching positive parent
   value to construct a path; it does not assume later policy validity.
5. `ParentSamples.v`, `ParentLoss.v`: twenty-four allocated parent-check paths
   (six accept, eighteen reject), arbitrary observations/waits, immediate loss,
   and loss after parsing and reaching the observation call.
6. `ParentPlan.v`, `Parent.lean`: agreement with the unchanged strict imported
   numeric parser and the actual launch-plan argument at index twelve.

The candidate's non-wait region bound retains the parser count, then adds the
parent continuation and existing `26*N + 4540` initialization bound. Waiting has
zero non-wait cost. Finite-prefix bounds do not imply unconditional termination
or elapsed-time bounds. A source rejection reaches the original `result_of` call;
it does not establish completed reporting, cleanup or process exit.

## Verification priorities and remaining work

The next agent should review before extending the proof chain:

1. Read complete public theorem types and transitive foundations, especially
   `parent_source`, `parent_initialization_source`, `numeric_validation_source`,
   `allocated_numeric_validation` and `allocated_validation_matching`. Inspect
   their definitions as well as the named theorem statements. Avoid substituting
   the matching witness for the universal failure-preserving contract.
2. Check the local external-effect model against the intended future Linux
   contract. `getppid` observations are unconstrained signed words; memory is
   unchanged locally. Concurrency, syscall implementation and libc are unproved.
3. Review source suffix boundaries, inherited continuations, the conditional
   getppid binding, output/input separation, arbitrary aliases that remain allowed,
   temporary-register frames, permissions, and prospective versus executed stores.
4. The composed frontier records an admitted parent endpoint existentially; it
   does not retain a persistent identity/liveness statement or an equality with
   the entire final event history. Check the explicit matching-path theorems and
   decide whether the advertised eventual contract needs a stronger trace link.
5. Add concrete cases for the complete numeric-to-initialization composition,
   including useful successes, early numeric failure, parent mismatch and later
   rejection ordering. Existing twenty-four parent cases and generic allocated
   witnesses do not replace that concrete whole-composition case table.
6. Add compiled mutations of the real parent guard/comparison and regressions for
   candidate inventory/identity validation. The preserved accepted gates retain
   their negative controls; this candidate does not yet add those new controls.
7. Remove or justify the unused `parent_getppid` helper and the unused `export`
   argument in `numeric_validation_contract`. In `allocated_parent_decision`, the
   existential cost bound may be chosen as the trace's own cost; it is a witness
   bookkeeping fact, not the independent complexity guarantee in `parent_source`.
8. Only after review, add the most-specific accepted architecture/decision/claim
   record, immutable initialization checkpoint snapshots, maintained gate and
   explicit transitive evidence amendments. Replay the complete dependency chain,
   preserve every prior theorem/artifact identity and update the roadmap only to
   the supported scope. Do not refresh expectations merely to hide a mismatch.

Main entry, mode-to-numeric composition, physical argv provenance, later setup,
pidfd/parent-death arming, supervision, cleanup, real Linux effects, compiler/
runtime/loader correspondence and hardware confidentiality remain outside this
candidate. The native helper SHA-256 remains
`fe20ad61706bb8e8463d32e5c9a1a9f3bf038ff52cc9f2ac40ba14c1a010d82c`.

## Reproduction

Use the repository-local tool wrappers and existing pinned environments. On this
workspace the dependency artifacts already exist. To independently replay from
the earlier stages, run the following sequentially from the repository root:

```sh
./scripts/check.sh
./scripts/check_m4.sh
./scripts/check_m4_connection.sh
python3 m4/bridge/check.py
python3 m4/controller/check.py
python3 m4/plan/check.py
python3 m4/main/check.py
python3 m4/policy/check.py
python3 m4/arguments/check.py
python3 m4/digest/check.py
python3 m4/validation/check.py
python3 m4/initialization/check.py
python3 m4/parent-checkpoint/verify.py
```

The candidate replay writes `.tools/m4/parent-checkpoint/report.json` and compares
it with `assurance/m4-parent-checkpoint-proof-output.json.gz`. Both contain full
types/foundations, source and artifact hashes, the preserved baseline identity,
and both strict export inventories. The caller-string closure has 161 entries;
the distinct numeric plan parser has 173. `--collect` writes an ignored candidate
report and never updates the tracked snapshot or the accepted claim manifests.

Fresh checkpoint receipts and their hashes are recorded separately in
`assurance/m4-parent-checkpoint-validation.json`. Read that receipt to distinguish
the checks rerun at this pause from the sixteen archived initialization receipts.
Independent statement review and promotion remain pending even when replay passes.
