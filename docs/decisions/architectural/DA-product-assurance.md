# DA-product-assurance: Deliver the Linux product with explicit platform trust

**Status: accepted planning revision, 2026-11-03, at the user's request.** Apply
[§AR-product.organization](../../architecture/AR-product.md#organization-organize-the-maintained-product-by-responsibility) to implement [§FS-linux-product](../../functional-spec/FS-linux-product.md#fs-linux-product-a-reusable-linux-workspace-with-an-explicit-trust-boundary).
Use [§AR-linux.bindings](../../architecture/AR-linux.md#bindings-explicit-os-contracts) for the primitive Linux interfaces.

## decision: Separate product delivery, application proofs and platform research

The previous M4 combined packaging a reusable product, proving all application
correspondence, proving Linux effects and connecting deployed binaries. Local
proof work accumulated while the public workflow still ran fixed VM cases.
The revised roadmap gives each of these outcomes its own acceptance contract:

- M4 delivers the reusable Linux product and verified executable core.
- M5 completes application-level control/authority correspondence against
  published Linux/runtime contracts.
- M6 reduces selected platform assumptions and develops hardware confidentiality
  and the named seLe4n backend as separately assigned tracks.
- M7 packages and supports releases whose claims match the completed evidence;
  it can start after the M4 product gate.

The initial trust boundary is [§FS-linux-product.trust](../../functional-spec/FS-linux-product.md#trust-platform-assumptions-for-the-initial-product).
Compiler/runtime and Linux assumptions are deliberate profile choices, with
conformance testing and artifact identity. Proof assistant checking remains a
requirement. Native adapter functions are explicitly tracked application trust,
not silently classified as part of the kernel.

## preservation: Keep the original assurance destination and evidence

This changes the delivery contract, not the truth of an existing theorem. The
original correspondence ledger and earlier M4 contracts stay available with their
original meaning. No entry becomes proved because a product accepts its boundary
as trusted. [§FS-assurance.product](../../functional-spec/FS-assurance.md#product-product-assurance-levels-and-trusted-components) records the product's separate assurance levels.

The parent contract in [§DA-m4-parent](DA-m4-parent.md#da-m4-parent-preserve-the-candidate-and-track-observations-in-composition) and the technical findings in [§DA-m4-routes](DA-m4-routes.md#da-m4-routes-expose-failed-central-connections-before-expanding-setup)
remain valid at their recorded boundaries. This decision supersedes their former
milestone scheduling: the route investigations do not block the product delivery,
and hardware confidentiality belongs to the platform research track.

Preserve the maintained compiler/reporting results for reuse when their premises
are supplied. Shipping with the selected GCC/Lean toolchain does not require
finishing the CompCert-to-deployed-binary research first. Any later distribution
of adapted compiler material must respect its recorded license.

## sequencing: Assign the next useful integration

The next worker owns the caller-policy VM workflow, root build entry and source
organization needed by it. It reuses the existing runtime, controller/helper,
policy and decoder proofs. Its acceptance is [§FS-linux-product.acceptance](../../functional-spec/FS-linux-product.md#acceptance-product-completion).
It must not substitute new datatype imports, kernel translation experiments or
another round of reviews for that delivery.

Application proof assignments follow the actual policy/launch, supervision and
publication boundaries of that product. Each one identifies the concrete code,
primitive assumptions and consumer theorem before implementation. Research is
assigned only with a specific assumption to remove and a bounded route decision.
