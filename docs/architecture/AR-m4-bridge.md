# AR-m4-bridge: Strict imported endpoint and source-byte correspondence

This package advances the checked connection required by [§FS-assurance.native](../functional-spec/FS-assurance.md#native-partial-m4-reporting-source-evidence)
for [§FS-workspace.results](../functional-spec/FS-workspace.md#results-entry-cancellation-and-bounded-transport). It preserves the live endpoint and every preceding
source proof. The public and private frame languages remain distinct.

## normalization: Exact computational endpoint

Give the public decoder a computational representation that does not depend on
error-message strings or unused diagnostic machinery. Ordinary Lean proofs must
show, for every byte array, that restoring the error strings gives exactly the
live decoder result. Preserve every successful field, every rejection and its
exact message, out-of-range byte behavior, and the full validity predicate.
An acceptance-only implication is insufficient for this normalization contract.

## import: Checked terms and explicit logical model

Export the complete transitive definition closure with a pinned Lean exporter.
Import it into a separate, pinned Rocq profile with error mode set to fail,
missing-quotient skipping disabled, and parsing-only mode disabled. Every imported
entry must retain kernel guardedness, positivity, universe and elimination
checks. Refuse an importer path that disables any of these checks. Independently
replay the resulting compiled module with the kernel checker.

Review the exact representation of natural numbers, bytes, arrays, propositions
and equality. The candidate importer uses SProp and definitional UIP; expose that
logical foundation in every applicable record. Kernel acceptance of a translation
alone does not establish its semantic correspondence with the original endpoint.
Record export provenance, importer patches, all transitive foundations and
unresolved translation obligations. Preserve upstream licenses and notices.

## bytes: Relate actual source bytes to the imported reader

Define explicit conversions between CompCert bytes and the imported Lean byte
representation. Prove that they preserve every byte value and list position.
Connect the imported arbitrary-offset, arbitrary-width little-endian reader to
an ordinary mathematical sum, then to the actual 32-bit and 64-bit source-reader
results. Respect machine widths, padding, bounds and memory ownership. Compose
with the established source-execution theorems; do not assume the desired reader
equality as an input premise.

## profile: Separate replay and remaining composition

Keep the established Coq/CompCert profile unchanged. Any newer checker profile
must rebuild the exact pinned CompCert source and selected project sources in a
separate local directory. Record unsupported-version flags, compatibility
changes and all source and artifact identities. Successful recompilation does
not transfer compiler or operating-system guarantees.

The next composition uses these primitives to connect actual reporting executions
through complete imported-frame decoding under [§AR-m4-bridge.frames](AR-m4-bridge.md#frames-complete-imported-frame-operations). Independent
translation-faithfulness review, controller ordering, Linux byte provenance, all
original native/Linux obligations, executable/runtime correspondence and hardware
confidentiality remain open until separately composed and reviewed. Reuse [§AR-m4-wire](AR-m4-wire.md#ar-m4-wire-source-connections-through-exact-report-bytes) and
[§AR-m4-public](AR-m4-public.md#ar-m4-public-exact-live-public-result-endpoint) without weakening their statements or refreshing their expectations
to hide a changed proof.

## frames: Complete imported frame operations

Extend the primitive connection to the actual imported array extraction,
byte-array equality, header checks, result fields, parser and validator. Prove
the operations for arbitrary inputs, including truncated slices, out-of-range
indices and malformed frames. Connect concrete source frames using their exact
byte layout; preserve the private sender's narrowing of the kind field and the
public decoder's two-byte interpretation. Preserve the exact rejection order
and the complete successful result, including the digest.

Compose only with established source executions and their explicit transport
observations. A frame-level theorem must not assume that Linux delivered the
bytes, that the controller called operations in the required order, or that the
imported representation is faithful merely because its terms type-check. Keep
those separate obligations visible until independently discharged. Preserve the
strict primitive bridge records when adding these results.
