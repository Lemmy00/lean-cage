# M4 source connections: report bytes across routines

This author source/proposition review advances [§AR-m4-wire](../architecture/AR-m4-wire.md#ar-m4-wire-source-connections-through-exact-report-bytes) for
[§FS-workspace.results](../functional-spec/FS-workspace.md#results-entry-cancellation-and-bounded-transport) from `34264901c9ca3a610eb8ea87351c230d3314b904`, following
[§FS-assurance.evidence](../functional-spec/FS-assurance.md#evidence-required-claim-record) and [§REQ-proof-integrity.statement](../requirements/REQ-proof-integrity.md#statement-review-the-proposition). It is not the independent
M4.6 composed-profile review. M4.2–M4.6 remain incomplete.

## Exact representation and private acceptance

`WireWords`, `WireFields` and `WireLayout` derive actual little-endian field and
digest projections from `outgoing_frame`, using the existing bit-exact writer/
reader proofs. All eighteen fields retain their machine widths; the kind's
one-byte narrowing is explicit. The reserved-tail predicate is equivalent to
zero export state, omitted count, digest, OOM count, PID count and export error.
The decoder also enforces its actual common fields and private tag conditions.
`WireValidity.wire_decoder_acceptance` equates actual decoder acceptance with
this independent field predicate for every 32-byte digest and machine-word input.

`WireDecoded` describes the actual output record: narrowed kind, retained decoded
fields and cleared private tail/digest. `WireSource.wire_decoder_source_return`
applies to every completed actual decoder history from independent input
ownership. It derives digest length from the actual 160-byte input contract,
returns the exact acceptance status, retains field mutation after a matching
header even on late rejection, preserves old memory on run/sequence mismatch,
and retains the actual fresh-local free witness.

## Actual paired source histories

`WireComposition.wire_source_observation_connection` takes an actual successful
sender history, its independent ownership and disabled source fault-selector
condition, and an actual decoder history whose owned buffer contains those
emitted bytes. The conclusion is the complete field-level decoder result. It
does not assume the desired decoder outcome. Errors, waits and loss remain in
both underlying machines; this completed-history connection asserts no fairness
or termination.

`WireRuns.wire_allocated_source_pair` constructs both owned memories and complete
actual histories for arbitrary fields and 32 digest bytes. Descriptor one disables
publication fault selection. Decoder acceptance or rejection is determined by
its actual checks. `WireSamples` instantiates this with ordinary exit, setup,
signal, UNKNOWN, private ADMITTED/ENTERED, raw kind 256 narrowing to zero, rejected
signal detail 65, CANCELLED and nonzero reserved data. These records are not
identified with the final public Lean language.

## Child-report and receiver connection

`WireFailure` proves that every selected child report has at most eight bytes;
an eight-byte observed prefix must be the complete packet, preserving its two
actual encoded words. `WireReceiverFields` derives stored setup fields from the
receiver's own read trace. `WireFailureReceiver.wire_failure_receiver_observation_connection`
combines actual child and receiver histories, explicit observed-byte equality
and an actually stored SETUP tag. It derives the full packet, the child's exact
stage/error fields, initial bad/entered zero, stage 1..8 and error 1..4095.

`WireFailureRuns.wire_failure_receiver_owned_pair` constructs complete allocated
histories with matching packet bytes, child exit request 125, arbitrary finite
receiver EINTR prefixes and close waits, and an ignored close error. The two
memories and ownership contracts remain explicit.

## Evidence and remaining boundaries

The inventory adds 72 Rocq declarations in fifteen modules: 1113 total across
212 maintained modules, with twelve unchanged Lean endpoints. The new baseline
is the preceding claim manifest byte-for-byte. All 1041 earlier full statements,
foundations and 197 compiled identities remain exact; four previous printing
contexts remain frozen. The complete bounded audit retains its 900-second
allowance and full M4.1, kernel, preservation and tamper checks.
`assurance/m4-wire-evidence.json` records the actual replay receipts.

The byte equality relates separate actual executions. It does not prove Linux
transport, descriptor/channel ownership, interference exclusion or the enclosing
program's call ordering. The checked C/Rocq-to-Lean bridge, all sixteen original
Linux/native entries, valid Linux wait-status provenance, runtime/compiler/
linker/loader correspondence, independent M4.6 review and M5 hardware channels
remain open. Native source, extracted AST, tool pins and VM profiles are unchanged.
