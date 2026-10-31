# AR-m4-public: Exact live public result endpoint

This package advances the public Lean end of M4.2 for [§FS-workspace.results](../functional-spec/FS-workspace.md#results-entry-cancellation-and-bounded-transport).
It uses the existing M3 decoder and keeps its source, interface and pins unchanged.
The preceding source-byte connections in [§AR-m4-wire](AR-m4-wire.md#ar-m4-wire-source-connections-through-exact-report-bytes) do not by themselves bridge
Rocq and Lean; this package must preserve that boundary.

## parser: Both directions for the live parser

Expose the actual private parser constant through a transparent proof alias.
A small elaborator constructs only a reference to that existing constant; ordinary
kernel checking must establish the alias's connection to the public decoder.
The helper adds no axiom, unsafe evaluation rule or translated parser assumption.

Prove an iff characterization of public success: exact 160-byte length, magic,
version, sequence and reserved header fields; entry and cleanup domains; every
returned field at its actual offset; and the live result-validity predicate.
The public kind uses two bytes, unlike the private decoder's one-byte kind.
Private ADMITTED and ENTERED tags remain excluded from final public success.
The theorem concerns decoding, not authenticity of guest or kernel observations.

## bytes: Widths and independent encoding

Connect the live little-endian reader to actual bytes at arbitrary offsets and
widths. Prove word truncation modulo its byte width, arbitrary surrounding-byte
preservation of the read value, and exact extraction of a selected byte window.
Derive all public field width bounds from successful decoding.

Define a proof-side public frame encoder independently from the parser. Prove a
complete round trip for records whose fields fit their actual widths and whose
digest has exactly 32 bytes. Include all public fields, entry, cleanup and final
reserved bytes. State validity as a separate necessary and sufficient condition;
do not assume every width-correct record is semantically valid.

## evidence: Additive claims and explicit bridge boundary

Audit all added Lean theorem full types and transitive axioms with ordinary kernel
checking. Preserve all 1113 preceding Rocq records, twelve preceding Lean records
and 212 compiled Rocq module identities, as well as archived receipts. Include
useful accepted frames and concrete rejections using ordinary checked proofs.
These endpoint results do not translate Rocq source semantics or certify Linux
transport, controller ordering, observation provenance or deployed executables.
The cross-assistant bridge, original native/Linux obligations and later M4/M5
assurance gates remain open until separately discharged.
