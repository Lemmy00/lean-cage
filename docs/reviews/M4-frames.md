# Complete imported frame and source-publication connection

This package follows [§AR-m4-bridge.frames](../architecture/AR-m4-bridge.md#frames-complete-imported-frame-operations) and [§REQ-proof-integrity.statement](../requirements/REQ-proof-integrity.md#statement-review-the-proposition) from
checkpoint `146a4b2fb39e7a397bef0c78bf1309c37053a2cb`. It retains the exact Lean
normalization, exported computational closure, strict importer and preceding
proofs. Its result concerns that imported logical endpoint. Semantic faithfulness
of the cross-assistant translation remains a separate review obligation.

The array proofs cover arbitrary lists, indices, slice bounds, concatenation and
equality. The byte-array copy and extraction proofs include truncation and
out-of-range behavior. Byte conversion is injective, so equality of imported
arrays reflects equality of their source bytes. No successful-slice premise
hides an unsupported case.

`FrameFields.imported_frame_fields` recovers every result field and the full
32-byte digest from an actual outgoing source frame. The kind is explicitly
`Int.zero_ext 8 (fr_kind r)`: the private sender narrows to one byte, whereas the
public parser reads two bytes. The remaining fixed header bytes, sequence,
length, payload and reserved fields are proved from the actual layout.

`FrameParser.imported_parse_view` and `imported_decode_view` preserve the exact
header, entry, cleanup and validation order for arbitrary imported byte arrays.
`FrameValidity.imported_frame_validity` proves the entire imported validity
predicate against ordinary integer comparisons and byte-list equality, for all
source records, digests and entry values. It includes tag-specific behavior,
UID/run relationships, export status/error relationships, digest rules and
knowledge bounds. The validator is not assumed as a premise of the final result.

`FrameComplete.imported_complete_frame` gives equality of complete decoder
results for every source record, sequence and 32-byte digest. Its result includes
the exact error code or every successful field. The earlier Lean restoration
proof preserves the associated error strings; that proof has not itself been
imported. `FrameLengths.imported_bad_length_rejected` rejects every byte list
whose length differs from 160, independently of its other contents.

`FrameExecution.source_sender_imported_frame` composes that result with actual
completed `send_frame` executions and their observed publication bytes when the
test fault selector is disabled. The general success theorem retains all test
publication modes. Prefix results retain the suffix obligation and reject wrong
lengths; they do not claim that a complete byte sequence proves successful return
or that a loss event proves failed parsing. Allocated executions establish
nonvacuity for arbitrary source fields. Memory ownership and the earlier source
semantics remain explicit premises.

Eighteen ordinary-kernel examples cover nine accepted and nine rejected cases,
and each is connected to an allocated actual sender execution. They include all
six public status tags, source kind 256 narrowing to EXIT, nonzero completed
export digests, export-error/UID bounds, private-only tags 5/6, invalid signal
detail, and the exact precedence of simultaneous header/entry/cleanup failures.
These source-kind examples do not alter the earlier public-encoder kind-256
rejection, where both kind bytes are encoded.

The gate preserves the original 42 Rocq records, 33 Lean records, 530 exported
declarations, 221 compiled identities and tool identities. The original primitive
manifests are retained byte-for-byte as `m4-bridge-primitives-claims.json` and
`m4-bridge-primitives-evidence.json`. New statement/foundation inventories and
replay receipts extend the active bridge manifests. The established Coq 8.18
profile, native source, pins and archived VM evidence are unchanged.

The imported logical model still exposes SProp and definitional UIP. Source
execution theorems retain the six existing Rocq foundation/semantic parameters.
No axiom, unchecked cast or admitted proof is added. This package does not prove
Linux delivered these bytes, establish whole-controller ordering, import the
normalization equality proof, certify the translation, or connect deployed
compiler/runtime artifacts. All sixteen original native/Linux obligations and
the later hardware channel work remain open. Continue with the controller and
translation obligations; this package does not complete M4.

The first final replay detected a different compiled identity for `FrameParser.vo`,
although its source, full statements and foundations were unchanged. Three direct
rebuilds agreed with the second identity. The two arithmetic proof-search calls
in that module were replaced with explicit order lemmas before recollection;
consecutive full replays must agree before accepting the new artifact map. The
failed receipt is retained. No earlier artifact identity or proof is relaxed.
