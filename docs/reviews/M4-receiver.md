# M4 source submilestone: complete terminal-error receiver

This author source/proposition review advances [§AR-m4-receiver](../architecture/AR-m4-receiver.md#ar-m4-receiver-complete-terminal-error-receiver-from-owned-inputs) and
[§FS-workspace.results](../functional-spec/FS-workspace.md#results-entry-cancellation-and-bounded-transport) from `7afee2c11f6f2db1fd65a972ed5b436db72eece0`, following
[§FS-assurance.evidence](../functional-spec/FS-assurance.md#evidence-required-claim-record) and [§REQ-proof-integrity.statement](../requirements/REQ-proof-integrity.md#statement-review-the-proposition). It is not the independent
M4.6 composed-profile review. M4.2–M4.6 remain incomplete.

## Independent inputs and complete source execution

`ReceiverInput.receiver_input` requires an aligned nonwrapping writable caller
result, writable TLS, and initialized actual run/UID globals outside the TLS
block. Descriptor, bad, entered, leader-done and status are arbitrary words.
Output can overlap old globals or TLS; only its final copy mutates that output.
No prepared path, successful transfer or selected result is assumed.

`ReceiverEntry.receiver_entry_prepared` constructs all seven actual allocations,
the descriptor store and the initial empty initialized byte prefix. The remaining
array and structure padding need not be initialized. `ReceiverReadHistory` covers
every finite read-loop execution, including retries, waiting, EOF, non-EINTR
failure and partial-read loss. It retains actual suffixes into terminal processing.
`ReceiverSelection.receiver_selection_source` follows every short-circuit branch
and all repeated actual `get32` calls. `ResultOwnership` adds old-permission
preservation for the existing constructor without changing that earlier proof.
`ReceiverConstruction` derives the selected constructor, both typed copies and
all seven frees in the actual environment order.

## Universal statements and concrete executions

`ReceiverProgram.receiver_program_guarantee` supplies memory preservation and
ordinary enabled progress or an exact return for every finite history of the
complete source. It uses the unrestricted existing effect machine. The internal
read invariant and terminal continuations are constructed from independent
inputs; their abstract composition lemmas are not public input assumptions.
`receiver_all_prefixes` protects old memory outside caller output and TLS.

`ReceiverOutcomes.receiver_return_trace_exact` classifies the actual read bytes
of each completed history, together with the source's stop reason and effective
bad flag. `receiver_read_nine_byte_bound` applies to every finite execution,
including partial-transfer loss. `ReceiverAccepted.receiver_actual_setup_bounds`
connects an actual SETUP kind load to exactly eight read bytes, initial bad and
entered flags zero, stage 1..8 and error 1..4095. `ReceiverFree` proves actual
free-list execution and the absence of permissions in all seven local ranges.

`ReceiverTerminal` retains every close result and discards its returned value.
`ReceiverRuns.receiver_complete_run` constructs a complete execution for every
owned input and every byte list of length at most nine, with any close reply.
`ReceiverFaultRuns` adds arbitrary finite EINTR prefixes and non-EINTR errors
after any prefix shorter than nine. Witness traces expose the actual retry and
close-wait segments. `ReceiverLossRuns` supplies partial-read loss after arbitrary
finite waits. `ReceiverWitnessInputs` constructs the required owned caller,
globals and TLS cells; it does not establish Linux initialization.

`ReceiverSamples` executes valid setup, short, ninth-byte, exit, signal, stopped
and raw-status cases. The setup witness completes after a close error. The
raw-status-65 witness returns SIGNALLED/detail 65, so a blanket 1..64 signal
claim would be false for this wrapper. The valid Linux wait-status provenance
needed by the intended `finish` domain remains explicit. Finite executions and
enabled progress do not establish fairness or termination.

## Evidence preservation and limits

The inventory adds 166 Rocq declarations across 43 modules: 1041 total in 197
maintained modules, with twelve unchanged Lean endpoints. The receiver baseline
preserves the preceding manifest byte-for-byte. All 875 earlier full statements,
foundations and 154 compiled identities remain exact, including the historical
compatibility closure. All three older printing contexts are frozen. The bounded
connection replay allowance grows from 600 to 900 seconds for the larger closure;
the M4.1 gate and all compilation, type, foundation, identity and tamper checks
remain mandatory. `assurance/m4-receiver-evidence.json` records exact receipts.

Remaining obligations include cross-routine selected-slice composition, the
checked C/Rocq-to-Lean bridge, valid wait-status provenance, all sixteen original
Linux/native entries, libc/Linux concurrency, compiler/runtime/linker/loader
correspondence, independent M4.6 review and M5 hardware channels. Native source,
extracted AST, tool pins and VM/kernel profiles remain unchanged.
