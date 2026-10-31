# AR-m4-wire: Source connections through exact report bytes

This package composes the source observations from [§AR-m4-sender](AR-m4-sender.md#ar-m4-sender-complete-frame-sending-and-publication-return-behavior),
[§AR-m4-decoder](AR-m4-decoder.md#ar-m4-decoder-complete-private-frame-decoding-from-owned-bytes), [§AR-m4-callers.failure](AR-m4-callers.md#failure-complete-child-failure-reporting) and [§AR-m4-receiver](AR-m4-receiver.md#ar-m4-receiver-complete-terminal-error-receiver-from-owned-inputs) for
[§FS-workspace.results](../functional-spec/FS-workspace.md#results-entry-cancellation-and-bounded-transport). It advances M4.2 through explicit byte relationships;
Linux transport, the public Lean endpoint bridge and complete controller/helper
composition remain separate obligations.

## fields: Recover the actual outgoing representation

Recover every outgoing 32-bit and 64-bit field from the source's 160-byte frame
and 32-byte digest. Preserve the distinction between the 144-byte structure and
wire offsets. The kind occupies one byte: its decoded value is the zero extension
of the low eight bits of the original 32-bit field. Do not assume the original
kind fits in a byte. Derive lossless kind recovery only from that explicit bound.
Retain exact run and sequence words, including wraparound values, and both fixed
reserved spans. State the private reserved tail's requirements over fields and
digest bytes, rather than assume that the decoder accepts an emitted frame.

## private: Exact private acceptance and rejection mutation

Characterize the actual private decoder using independently stated field checks:
expected run and sequence, narrowed kind, entry and cleanup ranges, expected UID,
zero triggers and the four private accounting fields, zero reserved tail, and
the actual per-tag conditions. Keep ADMITTED and ENTERED private tags. Do not
identify this language with the final public Lean result language.

A matching header causes output construction before subsequent payload/tag
checks. Its actual output retains the decoded fields, narrows the kind, and
clears the private tail fields and digest even if a later check rejects the
frame. A run or sequence mismatch rejects without changing old caller memory.
Every completed decoder execution retains the established actual local-free
postcondition. Successful publication alone does not establish acceptance,
entry, cleanup, final-public validity or transport authenticity.

## composition: Relate actual source histories with explicit provenance

Connect an actual successful sender return to an actual private decoder return
when the decoder's owned input contains precisely the sender's observed emitted
bytes. Use an independently stated source condition that disables publication
fault modes; descriptor one provides a concrete instance. Preserve the original
unrestricted sender/decoder semantics, including errors, waits and loss. The
connection is conditional on actual returns and does not prove termination.

Keep each routine's memory and ownership premises explicit. This observation
relationship does not prove that Linux delivered the bytes, prevent another
writer, identify pipe endpoints, or establish the controller's call ordering.
Construct allocated complete source pairs for arbitrary result fields and digest
bytes, with the actual accepted or rejected result. Include private control tags,
kind 256 narrowing to zero, signal detail 65, CANCELLED and nonzero reserved data.

## failure: Child failure words and completed setup classification

Relate a completed receiver's read trace to an actual finite child-failure
reporting trace explicitly. Every child trace is a prefix of its selected report;
its length is at most eight. If the receiver actually stores SETUP, its existing
source guarantee requires exactly eight bytes. Derive that these bytes are the
complete child packet and that the stored stage and error equal the child's
original machine words, with stage 1..8 and error 1..4095. Short, dropped and
partial shorter child reports cannot supply such an eight-byte SETUP result.

Construct complete owned child/receiver histories sharing the eight-byte packet,
with child exit request 125, arbitrary finite receiver EINTR retries and close
waits, and an ignored close error. Preserve the explicit provenance premise:
this is not a proof of Linux channel ownership or an upstream wait-status domain.

## evidence: Additive source connections and open bridge

Freeze all earlier full-statement printing contexts, preserve the 1041 preceding
Rocq and twelve Lean records and all 197 preceding compiled module identities,
and audit every added declaration, transitive foundation and source dependency.
Replay the maintained closure with ordinary kernel checking, the original M4.1
gate, tamper checks and the full repository gate. Normalize new sources before
collecting artifact identities. Record allocated source witnesses and the exact
assumptions of both connected histories.

These source connections do not translate Rocq terms or the live Lean definitions,
and they do not compose the whole deployed program. The checked C/Rocq-to-Lean
bridge, original sixteen Linux/native obligations, runtime/compiler/linker/loader
chain, valid Linux wait-status provenance, independent M4.6 review and M5 hardware
channels remain open. No native, dependency, VM or deployment profile changes.
