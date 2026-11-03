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

The caller-policy VM workflow, root build and source organization were delivered
at `92367a5` against [§FS-linux-product.acceptance](../../functional-spec/FS-linux-product.md#acceptance-product-completion).
The current assignment is [§RM-roadmap.m5.next](../../roadmap.md#m5next-current-assignment). Its acceptance is a source-connected
guest-entry guarantee, with the exact execution state in
[§FS-linux-product.proofs.entry](../../functional-spec/FS-linux-product.md#proofsentry-establish-actual-state-at-workload-entry). Keep the product workflow available while proving
or refactoring one live path at a time.

The M5 deliveries are guest entry, host-boundary safety, full policy authority,
owned lifetime/limits, and justified public observations/composition. Their code,
premises, consumers and acceptance are [§AR-application-verification](../../architecture/AR-application-verification.md#ar-application-verification-prove-the-application-through-integrated-security-guarantees). Platform
research is assigned only with a specific assumption to remove and a bounded
route decision. Earlier references to M5 hardware work belong to the historical
schedule; current hardware research is [§RM-roadmap.m6](../../roadmap.md#m6-platform-trust-reduction-and-confidentiality-research). The old proof records
retain their recorded content and theorem scope.

## refinement: Resolve implementation feasibility before expanding the proof work

The post-delivery review found that the three broad M5 regions did not settle
the source-to-proof route or account explicitly for all host/VM application
code. Reusing the M4 label for product delivery made its completion easy to
confuse with the old correspondence target. Keep the revised milestone meanings
fixed and describe the delivered guarantees by name in public documentation.

Prefer shared executable Lean control/security decisions over separately
maintained models. First resolve runtime/fork constraints and any necessary
native adapter connection through [§AR-application-verification.next](../../architecture/AR-application-verification.md#next-first-assignment-and-early-route-decision). The first
four working hours bound that investigation; they are not an estimate for the
complete entry proof. Preserve [§REQ-proof-integrity](../../requirements/REQ-proof-integrity.md#req-proof-integrity-never-substitute-a-weaker-claim-for-an-unfinished-proof): a multi-operation executor
cannot become trusted merely to make the route convenient. The same rule applies
to Python effects around a verified host decision core.

The current policy proofs establish acceptance/bounds of returned values, while
the recursive JSON implementation remains `partial`. Proving the byte-to-field
interpretation belongs to the policy-authority delivery. Entry needs a record
of actual credentials, handles, namespace/root/cgroup, filter and arguments;
the earlier receipt labels alone are insufficient. A valid host frame establishes
structural consistency; truthful inner observations need the later provenance
and composition result. These are named implementation obligations, not new
claims about the accepted product.

This refinement used a read-only planning assessment through the local
`claude-code` skill (configured model `claude-opus-5-5`, maximum effort) and
targeted inspection of the source/theorem statements. The existing matching
validation evidence was reused. It was a planning assessment, not a new full
security audit. Adopt its concrete coverage/parser/runtime concerns; retain
existing compatibility identifiers and proof rules rather than introducing an
automatic rewrite or a broader trusted executor. A native refactor may change
which earlier source proofs remain on the product path; preserve those results
at their recorded versions and update the live evidence map explicitly.

## delivery: Integrate the existing core through an owned VM transport

The implemented delivery uses the pinned kernel's second 8250 UART for private
control/results. It keeps boot logs and guest captures separate, transfers bounded
content-addressed snapshots/exports, and binds each result to a fresh request and
bundle identity. One request owns one disposable VM. Cancellation targets the
controller's helper by pidfd with parent/executable checks; VM teardown remains a
separate observation from helper cleanup. This needs no new kernel configuration.

Maintain the core under `lifecycle/` and `workspace/`, native code under `linux/`,
and host/typed interfaces under `python/leancage/` and `library/`. Compatibility
symlinks and existing Lean declaration names preserve earlier evidence; there are
no parallel implementation copies. The exact map, channel and bounds are
[§AR-workspace-vm](../../architecture/AR-workspace-vm.md#ar-workspace-vm-own-the-caller-request-disposable-vm-and-returned-artifacts). The [product handoff](../../reviews/workspace-product-handoff.md)
records completion of [§FS-linux-product.acceptance](../../functional-spec/FS-linux-product.md#acceptance-product-completion) and leaves the application
and platform proof tracks at their original assurance levels.
