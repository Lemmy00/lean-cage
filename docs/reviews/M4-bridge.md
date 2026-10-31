# Strict endpoint and primitive-reader experiment

This package follows [§AR-m4-bridge](../architecture/AR-m4-bridge.md#ar-m4-bridge-strict-imported-endpoint-and-source-byte-correspondence) and [§REQ-proof-integrity.statement](../requirements/REQ-proof-integrity.md#statement-review-the-proposition). It adds a
separate experimental checker profile to the public endpoint baseline at
`97871e3266adafd678238cecd55b8f0fcea5c3f4`.

The exact Lean normalization returns error codes computationally and restores
the four original error messages. Its final theorem states equality with the
live M3 decoder for every byte array, covering every returned field and every
rejection. The proof uses the actual private parser alias established by the
preceding package. The original M3 source and interface remain unchanged.

The pinned exporter supplies the complete computational decoder closure. The
strict importer checks it with guardedness, positivity, universes and elimination
checks enabled; missing-quotient skipping and parsing-only mode are disabled.
A negative trial verifies that the compiled plugin refuses disabled guardedness.
An independent kernel replay checks the resulting module. The imported decoder
has no exported axiom declarations, but its logical model uses SProp and five
instances of definitional UIP. Those foundations are explicitly audited.

The source connection proves actual byte-value conversion, list-position
preservation, arbitrary-offset/width little-endian reading, and exact 32-bit and
64-bit machine values. From owned readable memory, every completed source reader
returns the corresponding imported value with unchanged memory and exactly 59
or 103 source steps. Constructive executions allow arbitrary caller continuations.
Live prefixes retain progress, and loss remains possible at every prefix.
Allocated arbitrary four-byte and eight-byte inputs establish nonvacuity.

The profile recompiles the exact archived Clight AST, Codec and all 212 preceding
source-proof modules against the original pinned CompCert source under Rocq 9.3.
CompCert's advertised-version filter is bypassed explicitly; proof checks are
retained. The established Coq 8.18 tools and compiled artifacts remain separate.
GMP packages are extracted locally and the complete opam switch metadata is
pinned. Licenses and the importer patch are recorded in `m4/bridge/LICENSES.md`.

The first canonical replay checked 42 authored Rocq theorem records, 33 Lean
records including generated helpers, 530 exported declaration records, and 221
compiled identities in 173.728 seconds. These counts describe audit coverage,
not the strength of a security guarantee. Final maintained replay receipts,
full statements, foundations and identities are recorded in
`assurance/m4-bridge-claims.json` and `assurance/m4-bridge-evidence.json`.

The six inherited Rocq foundations remain visible in source-execution results.
The new Lean normalization uses quotient soundness and propositional
extensionality. The imported endpoint additionally depends on the declared
definitional-UIP model. Independent review of semantic faithfulness of the
cross-assistant translation is still required: accepting translated terms in a
kernel does not by itself prove that their interpretation matches Lean.

No complete public-frame bridge, transport authenticity, controller ordering,
Linux enforcement, compiler/executable/runtime chain or hardware confidentiality
is claimed. All sixteen original native/Linux obligations remain open. Continue
with full-frame and controller composition while preserving these boundaries.
