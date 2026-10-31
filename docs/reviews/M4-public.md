# M4 public endpoint: exact live decoding and complete encoding round trip

This author proposition/source review advances [§AR-m4-public](../architecture/AR-m4-public.md#ar-m4-public-exact-live-public-result-endpoint) for
[§FS-workspace.results](../functional-spec/FS-workspace.md#results-entry-cancellation-and-bounded-transport) from `ef594506208da88a807b485f0ee3072ccf2886c1`, following
[§FS-assurance.evidence](../functional-spec/FS-assurance.md#evidence-required-claim-record) and [§REQ-proof-integrity.statement](../requirements/REQ-proof-integrity.md#statement-review-the-proposition). It is not the independent
M4.6 composed-profile review. M4.2–M4.6 remain incomplete.

## Live parser and both directions

`PublicWire.parserView` aliases the actual existing private M3 parser constant.
The elaborator and unfolding macros only construct references to that constant;
ordinary Lean checking verifies all generated proof terms. `live_decode_view`
connects the alias to the actual public `decodeResult` by kernel equality.
`parserView_iff` and `decodeResult_iff` prove both directions over arbitrary byte
arrays and result records. Successful decoding requires the actual header,
entry and cleanup domains, every field at its actual offset and the live
`resultValid` check; the reverse direction proves these conditions suffice.
There is no assumed parser translation or additional axiom.

`headerBad_iff` exposes size 160, magic, version, sequence zero, payload length
128 and both reserved words. `little_bounded`, `fields_widths` and
`accepted_widths` derive every machine-width bound from actual bytes. Kind has
the public two-byte width; entry and cleanup are checked separately.

## Independent byte encoding and round trip

`PublicCodec` relates the live reader to a list-based little-endian value,
proves arbitrary-width word encoding modulo its actual byte width, and proves
exact reads and extraction in arbitrary surrounding bytes. The independent
`PublicEncode.frameBytes` includes all public fields, the 32-byte digest and
reserved bytes. Each projection is derived from the generic word/window results;
no result-field equality is assumed.

`frame_fields` recovers the original record under explicit `Widths r` and
`r.exportDigest.size = 32` premises. These premises constrain representation,
not semantic acceptance. `decode_encode` proves that the actual public decoder
of the encoded frame is exactly `validateResult r`. `decode_encode_iff` then
states that success is equivalent to the actual semantic validity check.
The encoder is proof-side infrastructure; native and M3 runtime sources are
unchanged.

## Nonvacuity and public/private distinction

Ordinary kernel proofs construct accepted EXIT(42), SETUP(8,13), SIGNAL(9),
CANCELLED, UNKNOWN and PREFLIGHT records. Separate witnesses reject private
ADMITTED/ENTERED tags, signal detail 65 and kind 256 encoded in the public
**two-byte** field. This last encoding is different from the private sender's
one-byte truncation of an original kind 256 to zero. The witnesses establish
useful public behavior and concrete rejection without claiming the two decoder
languages or encodings coincide.

## Preservation and assurance boundary

The inventory preserves all 1113 preceding Rocq and twelve Lean theorem records,
including full types and foundations, and all 212 compiled Rocq identities.
It adds 91 Lean records: 67 authored theorems and 24 generated equation/proof
helpers. All are audited, with only the already reviewed Lean foundations
`propext`, `Classical.choice` and `Quot.sound` permitted. The gate rejects omitted
maintained Lean source files. `assurance/m4-public-evidence.json` records replay,
tamper checks and the full repository gate.

These are endpoint proofs in Lean, not a translation of Rocq terms. The checked
cross-assistant bridge, actual Linux byte/observation provenance, whole-program
ordering, all sixteen original native/Linux entries, compiler/runtime/linker/
loader correspondence, independent M4.6 review and M5 hardware channels remain
open. Original source, extraction, CompCert/Lean pins and VM profiles are unchanged.
