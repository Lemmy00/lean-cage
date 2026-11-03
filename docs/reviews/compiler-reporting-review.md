# Compiler/reporting integration review — 2026-11-03

Reviewed implementation: `fe96f1676f04907df8e398997fa6a9905e62c483`, including
the output-capture correction `34d6dae`, source/Lean connection `d8af5b5`, and
integrated development rules. This is a focused source/statement/integration
review under [§REQ-proof-integrity.statement](../requirements/REQ-proof-integrity.md#statement-review-the-proposition).

## Result to preserve

The capture correction makes storage failure sticky: the destination is closed
and disabled, while subsequent draining cannot append a later fragment to the
stored prefix. Its native regression exercises partial writes, interruption,
failure and the actual frame/Lean report path. The VM evidence includes the
updated helper and retains observed termination and output-loss semantics.

`CurrentSource.current_sender_decodes` connects the current complete-helper
reporting call to the checked decoder interface. The ordinary Lean consumer is
`LeanCage.Reporting.live_publication`; its imported normalized proof is consumed
by the source theorem. The complete types and logical foundations are recorded
in `assurance/reporting-connection.json.gz`.

`CompilerCertificate.current_compilation` establishes a concrete compilation
equation. `current_assembly_reporting` consumes it through the actual backend
pass simulation and the source reporting argument. `compiled_reporting_contract`
states emitted-prefix preservation for finite assembly runs and the decoder
equation for a successful return. The proof supplies source progress before
using the compiler simulation in the reverse direction.

The source is the helper's Clight program plus an explicit logical errno object.
The caller must supply the compiled/source state match, owned inputs and the
primitive runtime contract. The target is an identified assembly model; the
deployed helper still follows its existing native build. These precise interfaces
make the work reusable for the application/platform tracks in the revised plan.

## Review conclusion and validation

No implementation or theorem-statement correction was identified in the reviewed
capture/reporting/compiler changes. The source of confusion was the delivery
contract: a useful conditional component had been presented as the endpoint of
an assignment to finish the whole platform chain. The revised product and
application contracts in [§FS-linux-product](../functional-spec/FS-linux-product.md#fs-linux-product-a-reusable-linux-workspace-with-an-explicit-trust-boundary) resolve that planning mismatch.

`./scripts/check_m4_all.sh` passed with exit code 0 on 2026-11-03. Its current-profile
route checked the source and reporting/compiler connections, reused matching proof
artifacts, passed the live capture/publication regression and verified retained VM
artifact identities (60 cases, three API checks and six death/cancellation cases).
Grund consistency and formatting also passed. The transcript is local at
`.tools/assurance/product-replan-check.log`. No fresh VM workload replay was needed
for this documentation-only revision. Subsequent prose corrections use only the
documentation/whitespace checks; the proof and runtime inputs remain unchanged.

The existing proof snapshots and original correspondence ledger are preserved.
Their conditional results are inputs to the next work; they are not a reason
to redo the accepted parent or reporting components.
