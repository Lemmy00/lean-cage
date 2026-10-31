# M4 source submilestone: actual callers and complete child-failure reporting

This author source/proposition review advances [§AR-m4-callers](../architecture/AR-m4-callers.md#ar-m4-callers-actual-source-call-composition) and
[§FS-workspace.results](../functional-spec/FS-workspace.md#results-entry-cancellation-and-bounded-transport) from `26c858ec9391181fc958300e8f8b79a89ac6a849`. It follows
[§FS-assurance.evidence](../functional-spec/FS-assurance.md#evidence-required-claim-record) and [§REQ-proof-integrity.statement](../requirements/REQ-proof-integrity.md#statement-review-the-proposition). It is not the independent
composed-profile review. M4.2–M4.6 remain incomplete.

## Actual caller composition

`CallContexts.plug_clight_step` and `unplug_clight_step` prove continuation
replacement against real Clight steps, including nested calls, labels/gotos,
loops, switches, expression judgments, allocation, stores and frees. Replacement
requires a genuine call continuation and ends at the local return boundary.
`plug_library_step` and `unplug_library_step` retain the original byte/TLS effects,
library effects, partial-copy or I/O loss, waits and asynchronous loss. They do
not substitute a function oracle for the source. `caller_run_decomposition`
classifies every finite caller run as a callee prefix or a genuine callee return
followed by caller execution, with the same events and memory.

`WriteCallers.write_caller_decomposition` instantiates this with the preserved
complete `write_all` source theorem. It retains initialized packet ownership,
exact emitted prefixes, full-success versus failed-return conditions and the
actual caller continuation. The general progress, event and prefix combinators
are constructed from those source runs; an assumed callee postcondition does
not support the public child-failure theorems.

## Complete child-failure source

`FailureMemory.failure_prepare_execution` constructs the actual eight-byte local
allocation and both complete `put32` calls from independent memory. It executes
96 Clight steps before the first `fault` call, preserves all previously valid
memory, and derives the initialized little-endian packet for arbitrary 32-bit
stage/error words. A signed error argument is converted by the actual source
cast; its word bits are retained. The descriptor is arbitrary. The local buffer
is fresh and separate from the independently writable TLS cell.

`FailureContract.failure_input` requires owned stable NUL-terminated mode and
literal strings, the actual source-global pointer and symbol identities, and
representable writable TLS. It does not require a desired fault outcome,
successful reporting, an execution certificate or a final result. The two source
fault calls are proved using the maintained `fault` body. Actual branching selects
no report for `error_drop`, three bytes for `error_short`, and eight otherwise.
All source statements, the complete write loop and the `_exit(125)` call remain.

`FailureSafety.failure_all_prefixes_defined` supplies an enabled ordinary step
at every finite live prefix of the complete function. It retains arbitrary waits,
EINTR histories, errors and process loss; it does not establish termination.
`failure_never_returns` excludes a local return. The generic continuation theorem
retains the caller boundary. `FailureTrace.failure_reporting_prefix` proves that
every complete-source history emits a prefix of the selected packet, including
bytes transferred during interruption. `FailureExit.failure_only_exit_125`
constrains every observed exit request to code 125. A returned zero-transfer or
failed write proceeds through the same post-write source continuation, which
ignores that return value and attempts exit.

`FailureRuns.failure_successful_exit_exists` constructs an actual source run to
exit for every owned input. `FailureError.failure_failed_report_exit_exists`
includes a real non-EINTR failure event and the subsequent exit request;
`failure_partial_loss_exists` retains arbitrary finite waits followed by transfer
loss and the actual terminal memory. `FailureWitnesses` allocates the actual
literal blocks 21/23, mode pointer block 75, its mode string and independent TLS.
It supplies normal, dropped, short, failed and lost executions for arbitrary
argument words. Its bounded mode-string witness is not a bound on the universal
input contract. These are inhabited local input states, not whole-program
initialization, frontend correctness or execution of the deployed binary.

The source has no explicit local-buffer free before `_exit`; the proofs do not
invent one. A modeled exit event terminates the local machine. No Linux resource
reclamation, descriptor cleanup, publication receipt or end-to-end isolation
follows from that local contract. Loss preserves the actual interruption memory.

## Replay and remaining obligations

The active audit contains 494 Rocq declarations and the unchanged 12 Lean
endpoint claims. All prior 373 complete declarations/assumptions and all 27
compiled artifacts are retained. The 21 new modules bring the kernel replay to
48 modules. Twenty-three evidence-gate regressions check inventory, omission,
full-statement/foundation/artifact drift and invented obligation closure.
The inventory is printed in groups of at most 100 declarations to preserve the
existing per-command limits; no type truncation or axiom policy changes.

`assurance/m4-callers-baseline-claims.json` snapshots the exact previous manifest.
`assurance/m4-callers-evidence.json` binds full statements, sources, compiled
artifacts, preservation checks and raw command receipts. Explicit documentation
fingerprint and transitive evidence bookkeeping amendments preserve all previous
proof records, frozen native/extracted/preprocessed source and AST, pins, VM
artifacts and historical receipts. No hostile host or fresh VM workload is run.

Frame construction/decoding, its partial rejected-frame output mutation,
`finish`, terminal reception and whole-slice caller composition remain open.
So do the checked C/Rocq-to-Lean bridge, all sixteen original native/Linux entries,
actual libc/Linux interference, compiler observation/refinement, executable and
runtime chain, independent M4.6 review and M5 hardware confidentiality.
