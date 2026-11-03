# AR-reporting: Connect native reporting calls to the live Lean decoder

This connection implements the source-to-decoder edge of
[§FS-workspace.results](../functional-spec/FS-workspace.md#results-entry-cancellation-and-bounded-transport) and the evidence boundary of [§FS-assurance.native](../functional-spec/FS-assurance.md#native-partial-m4-reporting-source-evidence).
The producer is the maintained helper's `send_frame` call on descriptor 1.
[§DA-reporting-connection](../decisions/architectural/DA-reporting-connection.md#da-reporting-connection-connect-reporting-through-a-checked-call-interface) records this whole-call proof boundary.
The consumer is `LeanCageM3.decodeResult`, through the ordinary Lean theorem
`LeanCage.Reporting.live_publication`. Check their integration with
`./scripts/check_reporting_connection.sh`.

## interface: Preserve the complete call observation

The source input is an owned result structure, its 32 digest bytes, selector/TLS
storage and a call continuation. The source execution uses the current complete
helper's Clight program, its actual globals, the existing byte-aware library
effects and asynchronous loss. Its observation retains every emitted byte and
classifies the call as running, published, failed or lost. Internal execution,
retry and wait events may be erased by this whole-call interface; their permitted
executions must remain in the source producer's quantifiers.

The shared `Call` relation records the untransmitted suffix. A published call
has an empty suffix. Failure or loss may occur at any prefix, including after
the complete frame was emitted. Do not infer that loss necessarily makes the
decoder reject, or that a complete frame proves clean termination.

The shared `FrameView` relates bytes to their header, raw entry and cleanup tags
and every public result field. The source producer must establish these byte
equations, rather than assume the decoder's result. Preserve source-width
truncation, malformed tags, error precedence, digest bytes and all validation
failures. The ordinary Lean consumer applies the existing live decoder; it must
not substitute an independent parser for that endpoint.

## proof: Check the interface in both proof environments

Export the ordinary Lean proof of the shared normalized publication statement,
including its proof term. Extend the accepted computational import using the
unchanged strict importer. Reuse a prior declaration only after checking its
identity; retain the original export and every transformation. Keep all kernel
checks enabled. Establish explicit byte/list, frame-field and status conversions,
with named constructor equations, between the source semantics and this shared
interface. The source reporting theorem must consume the imported Lean theorem.

Recheck source consumers against the current complete helper program. Preserve
the original extraction and its proof sources. A proof-only adapter may name a
composite already proved present in the actual program, avoiding repeated
normalization of its proof fields; its lookup and member equations must be
kernel checked. Do not replace the actual global environment with the smaller
historical extraction.

Include a useful source execution and incomplete, failed and lost observations.
Audit complete theorem types, transitive foundations and the interface's compiled
declarations. A changed entry/cleanup conversion must fail the source connection.
Use matching checked artifacts for unchanged dependencies under [§AR-tooling.checks](AR-tooling.md#checks-one-development-gate).

## boundary: Supply the remaining implementation producers

This call interface describes the retained byte-aware source semantics. The
physical ownership/global-state producer, pinned Linux I/O and partial-copy
relation, controller/supervision/export composition and compiler/runtime/loader
chain remain required by [§FS-assurance.native](../functional-spec/FS-assurance.md#native-partial-m4-reporting-source-evidence). The source call proof does not
supply them. The original obligation register retains its original scope.
