# AR-m4-decoder: Complete private-frame decoding from owned bytes

This package develops the decoder boundary in
[§AR-m4-callers.decoder](AR-m4-callers.md#decoder-decoder-composition-boundary) and [§AR-m4-native.contract](AR-m4-native.md#contract-intended-universal-simulation-and-ownership-obligations) for
[§FS-workspace.results](../functional-spec/FS-workspace.md#results-entry-cancellation-and-bounded-transport). It targets the maintained `decode_frame` body, including
its failures and writes. Completing an auxiliary memory or source-path lemma
does not complete the routine or the M4 milestone.

## input: Independent frame and output ownership

Own all 160 initialized readable input bytes at a representable, nonwrapping
address. Own an aligned, writable, nonwrapping 144-byte result object and the
actual source-global run, UID, preflight and magic-literal values. Keep input
bytes and the globals needed after output construction separate from the
output writes. Derive every byte and word read from this ownership; do not
assume a valid header, accepted tag, successful return or source execution.

Use the actual 32-bit and 64-bit words and source casts. The result object is
not the 160-byte wire frame. Its padding need not contain initialized bytes.
Do not strengthen the local library contract into an actual libc/Linux claim.

## source: Actual construction and validation

Execute the actual local allocation, comparison, short-circuit checks, reader
calls, loops, field stores, structure assignment and local free. The comparison
retains arbitrary signed nonzero results and arbitrary waits. Its zero result
is determined by the owned first four frame bytes and magic bytes.

Header checks cover magic, version, header reserved bytes, run identity,
sequence, payload length and the last four reserved bytes. Header rejection
returns -1 before writing the caller's output. Passing the header builds the
actual result fields from the wire offsets and initializes the omitted fields
and digest to zero. The structure assignment occurs before the remaining
payload and tag checks. Rejection at those later checks returns -1 with that
output mutation; no transactional failed-decode claim is permitted.

Retain every common payload check and the full zero-byte loop over offsets
96 through 155. The accepted tags and per-tag constraints are exactly those in
[§AR-m4-native.contract](AR-m4-native.md#contract-intended-universal-simulation-and-ownership-obligations): tags 0, 1, 2, 4, 5, 6 and 7, with tag 7 additionally
requiring the source preflight flag. Tag 3 and all other arbitrary tag bytes
reject. This private intermediate parser remains distinct from the public
Lean result parser.

## prefixes: Memory and observation boundary

Prove the ordinary enabled-step or exact-return alternative for every finite
live prefix, including malformed inputs. Retain arbitrary comparison waits and
process loss at every source boundary, with the actual memory at that boundary.
Record preservation outside the caller's output and fresh local storage, and
the actual free on every return. No waiting-time or Linux scheduling guarantee
follows from a finite source-path proof.

The generated structure assignment is one Clight step. Its copying of padding
memory values is not a claim that those padding bytes are initialized, nor a
claim about interruption granularity in a compiled executable.

## evidence: Full-source evidence and inhabited inputs

Follow [§AR-m4-callers.evidence](AR-m4-callers.md#evidence-additive-replay-and-claim-boundary) and [§FS-assurance.evidence](../functional-spec/FS-assurance.md#evidence-required-claim-record). Include complete
statements and foundations, source and compiled identities, actual allocations
and useful accepted and rejected executions. Keep construction, early rejection,
later rejection and the complete routine as distinct claims until composed.
Preserve all preceding evidence. The checked C/Rocq-to-Lean bridge, complete
slice, Linux effects, executable chain, independent review and hardware
confidentiality remain separate obligations.

The decoder package also repairs the caller package's dependency closure:
fifteen imported historical module names had source only in the ignored build
directory. Preserve those exact sources under maintained compatibility paths,
include every declaration and compiled identity in the gate, and reject any
unlisted local proof import. The previous caller receipt established the local
kernel check but did not establish replay from only maintained inputs. The new
receipt must identify this limitation and the repair explicitly.
