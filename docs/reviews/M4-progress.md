# M4 continuation: checked local effects, open correspondence

This continuation follows [§RM-roadmap.m4.packages](../roadmap.md#m4packages-correspondence-work-after-the-reviewed-m3-baseline) and [§AR-m4-native.revision](../architecture/AR-m4-native.md#revision-byte-aware-effects-and-loss-before-the-lean-bridge).
It advances [§AR-m4-effects.memory](../architecture/AR-m4-effects.md#memory-local-byte-and-errno-contracts), [§AR-m4-effects.machine](../architecture/AR-m4-effects.md#machine-source-steps-blocked-calls-and-loss) and
[§AR-m4-effects.lean](../architecture/AR-m4-effects.md#lean-exact-public-result-and-knowledge-endpoints). M4.2–M4.6 remain incomplete under [§REQ-proof-integrity.statement](../requirements/REQ-proof-integrity.md#statement-review-the-proposition)
and [§FS-assurance.closure](../functional-spec/FS-assurance.md#closure-rules-for-stronger-claims). The implementation does not supply full native
simulation, kernel verification, executable correctness or production isolation.

The subsequent [write-loop source review](M4-writeall.md) completes the local
[§AR-m4-effects.writeall](../architecture/AR-m4-effects.md#writeall-universal-source-loop-connection) submilestone: every finite actual `write_all` execution
has prefix safety, defined execution and exact returns under the byte-aware
effect contracts. It adds 95 checked Rocq declarations and source-connected
nonvacuity witnesses. The original effect-layer snapshot below is retained as
historical evidence; its missing `write_all` connection is now supplied, while
whole-slice simulation and the checked Lean bridge remain open.

The later [reporting-primitives review](M4-primitives.md) and
[writer/round-trip review](M4-writers.md) add checked source errno normalization,
byte readers/writers and codec round trips. The current inventory has 227 Rocq
and 12 Lean declarations. The snapshots below retain their original scope.

## Delivered evidence

The additive `m4/connection/` package defines byte-aware effects with actual
CompCert `Mem.loadbytes`, `Mem.storebytes` and `Mem.store Mint32` operations. It
requires bounded owned buffers, representable offsets and a separated aligned
errno cell. Positive transfer sizes come from the transferred bytes and are
bounded by the request. Read bytes are arbitrary; write bytes come from memory.
Successful/zero calls may preserve or update errno. Errors store arbitrary Int32
errno and return signed -1, so EINTR is retained without a progress assumption.

The checked facts include return bounds, exact read contents, preserved write
buffers, unchanged memory outside the read prefix/errno cell and deterministic
memory for the same complete reply. Real CompCert allocations inhabit the read,
short-transfer, signed-error and write contracts. These local model results do
not prove Linux or libc implements the contract.

The environment product uses actual internal Clight `step2` transitions, with a
guard that excludes every stock external-call transition. Exact equations match
the maintained source's read/write/errno signatures and source call lists.
Read/write/errno are the only implemented external returns. Blocking may repeat
arbitrarily, every live source state may lose the process, and loss during a read
or write retains the transferred bytes without a return to C. Constructive partial
read/loss witnesses and terminal dead states rule out a synthetic success receipt.
Unsupported `close`, string/memory routines and `_exit` remain unimplemented
semantics; no whole-function safety result is inferred from those missing steps.

The Lean endpoint lemmas use the exact existing M3 definitions: arbitrary
observation traces need a real `execObserved` event to establish entry, retain
known entry after loss, and require extinction before release. Actual accepted
final frames satisfy `resultValid` and cannot use ADMITTED/ENTERED tags 5/6.
Original reachable lifecycle receipt order is retained. These are additional
model lemmas, not a checked translation of the Rocq semantics into Lean.

## Assumptions and preserved evidence

The new manifests record full theorem types and transitive assumptions. No new
authored axiom, admission, unfinished theorem or compiler-trust proof shortcut
supports the new results. Rocq and Lean foundations are recorded separately.
The effect/loss event system is deliberately separate from CompCert's upstream
trace semantics; no compiler theorem is claimed for this extension.

155 of the 156 M1–M3 baseline files remain unchanged, including original native
helper/filter bytes, Lean statements, pins and VM records. The remaining file is
the decision index, extended only with the link required by Grund. Original M4.1
proof sources and its complete
theorem/type/assumption expectations are preserved. Its roadmap/index source
hashes advance only for the explicit progress links; the baseline decision-index
amendment and continuation evidence record old/new identities and the reason.
No theorem, axiom or deployed guarantee expectation changes. No stale VM replay is relabeled
as current proof evidence and no fresh workload runs on the shared host.

The claim/evidence register is additive under [§FS-assurance.evidence](../functional-spec/FS-assurance.md#evidence-required-claim-record) and
[§AR-m4-effects.gate](../architecture/AR-m4-effects.md#gate-additive-evidence-and-completion-boundary). The sixteen original correspondence entries are individually
retained in `assurance/m4-obligations.json`; none is marked discharged by these
local effect proofs, endpoint lemmas, source maps or artifact hashes.

## Validation

The final command results and raw receipts are recorded in
`assurance/m4-connection-evidence.json` and `assurance/m4-connection-check.log`.
Run Grund formatting, `./scripts/check.sh`, `./scripts/check_m4_connection.sh`,
`python3 scripts/run_m3_vm.py --check-artifacts` and `git diff --check`.
The repository gate passes 74 Python tests and 168 Lean guards, preserving the
445/274/419 M1/M2/M3 declaration inventories and all 60 M3 named claims. The new
package checks 31 Rocq theorems and 12 Lean theorems; all new Lean proofs depend
only on `propext` or no axioms. The Rocq dependency union retains the six distinct
foundations/semantic parameters already audited by M4.1; no new authored axiom is
introduced. `coqchk` rechecks the terms. Seven evidence regressions cover stale
sources, changed types/assumptions, omitted/empty claims, missing/duplicate original
obligations and invented completion. The original M4.1 gate still checks its
25 Rocq declarations, 12 Lean targets and 11 source witnesses.

M3 artifact revalidation matches all 70 artifacts and the preserved 60-case,
three-API, six-death/cancellation record. Artifact revalidation is distinct from a fresh VM run. Since the baseline native,
Lean and VM inputs do not change, these additions do not require new hostile
workload execution.

## Remaining critical path

1. Complete the selected actual C slice's universal simulation and memory safety,
   including errno evaluation, partial result mutation on rejected frames,
   local allocations, framing, terminal receive and failed publication. The local
   `write_all` theorem now covers all its finite source executions under the new
   effect semantics; composing it with callers remains open. The stock
   Clight/compiler semantics is not certified by that extension.
2. Check the connection from C executions and private-event assembly to the exact
   Lean final decoder and lifecycle observations. Existing endpoint lemmas are
   useful targets; they do not assume or prove this missing relation.
3. Expand through the real controller/helper composition (M4.3), then discharge
   each relevant pinned Linux implementation/transitive dependency (M4.4).
4. Connect the actual GCC-built helper, Lean/native runtimes, linking, loaders,
   kernel and deployment artifacts (M4.5). A stock CompCert theorem does not cover
   GCC or the extended event system. Hash identity is not executable refinement.
5. Compose and independently replay a named profile (M4.6). Open Linux or compiler
   work cannot be turned into accepted foundational trust to claim completion.

No M4 completion or security guarantee is upgraded. M5 hardware channels remain
separate and open. Completing the remainder requires the missing proofs above;
passing the present gates is not a substitute.
