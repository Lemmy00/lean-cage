# Next assignment: deliver the reusable Linux workspace product

**Delivered on 2026-11-03.** The [product handoff](docs/reviews/workspace-product-handoff.md)
records the accepted root workflow, libraries, bundle/trust manifest and validation.
The assignment below remains its acceptance contract. Further application
verification follows [§RM-roadmap.m5](docs/roadmap.md#m5-verify-the-complete-application-control-path).

The current plan is [§RM-roadmap.m4.next](docs/roadmap.md#m4next-current-m4-continuation), revised on 2026-11-03.
Read [§FS-linux-product](docs/functional-spec/FS-linux-product.md#fs-linux-product-a-reusable-linux-workspace-with-an-explicit-trust-boundary),
[§DA-product-assurance](docs/decisions/architectural/DA-product-assurance.md#da-product-assurance-deliver-the-linux-product-with-explicit-platform-trust),
AGENTS.md and the [compiler/reporting review](docs/reviews/compiler-reporting-review.md).
Continue from the latest reviewed `main`. Reuse the implementation and evidence;
start with fresh task context rather than rebuilding prior work.

## Delivery contract

**Before:** an operator can build a CLI inside a milestone directory and run a
VM harness with fixed workloads. A general caller cannot yet supply its own
supported policy and receive its run's report, captures and export through one
root interface.

**After:** one documented root build stages LeanCage and its supported VM profile.
The CLI and reusable library accept a supported caller policy and bounded input
snapshots. `check`, `run` and `report` execute that request in the disposable VM
and return its report/artifacts. Maintained product code has functional homes,
and the bundle identifies the exact checked core and trusted components.

**Consumer:** a developer or AI-agent integration running its own offline shell
or Python task. **Acceptance:** [§FS-linux-product.acceptance](docs/functional-spec/FS-linux-product.md#acceptance-product-completion), exercised through
that public interface on the final changed inputs.

Carry this whole assignment through implementation, validation, commit and push.
Do not stop after documenting an interface, adding a wrapper or proving a helper
lemma. Work in small commits, while treating the usable workflow as the delivery.

## Existing components to use

- `m3/Main.lean`, `m3/LeanCageM3/API.lean`, policy/result modules and their proofs
  are the current application entry and reusable core.
- `native/leancage_m3.c` implements the Linux helper. Its sticky capture-failure
  correction is in `34d6dae`; preserve the public report regression and VM cases.
- `profiles/m3/`, `scripts/run_m3_vm.py` and the recorded VM configuration provide
  the runtime lock, preparation, image-building and execution baseline.
- `verification/reporting/` and `verification/compiler/` supply reusable checked
  reporting components. Their normal gates reuse matching artifacts.
- Parent/input validation was accepted before this assignment. Its existing
  contracts and checks are prerequisites, not new review tasks.

The current native filenames above are navigation to existing code, not a template
for new names. Follow [§AR-product.organization](docs/architecture/AR-product.md#organization-organize-the-maintained-product-by-responsibility) for consolidation.

## Implementation sequence

1. Inventory the actual runtime dependencies and define the target component map:
   portable policy/lifecycle/workspace/reporting library, product CLI, Linux
   adapter, profile bundle, VM runner and verification tools. Migrate maintained
   product paths/imports/build recipes coherently. Preserve declaration aliases or
   historical regression inputs where needed for evidence; document one migration
   map. A new wrapper around unchanged milestone packages alone is not completion.
2. Provide the root build and bundle recipe. The controller, native helper,
   runtime, kernel/configuration and manifest must be the ones exercised by the
   workflow. Keep pinned tools local. Reuse existing dependencies and policy
   formats; introduce no new general-purpose policy language.
3. Specify and implement the VM request/result transport under
   [§FS-linux-product.transport](docs/functional-spec/FS-linux-product.md#transport-carry-requests-and-results-across-the-vm-boundary).
   Map caller-owned policy/input snapshots into the existing in-VM CLI. Separate
   guest output and boot logs from trusted control/result framing. Return bounded
   artifacts safely. Implement cancellation, channel loss and teardown ownership.
4. Connect the same core to the public CLI and library. Map each advertised proof
   to the actual definition consumed in that path. Prove missing core/adapter
   properties within the contract; preserve prior theorem statements and explicit
   assumptions. Publish the initial trusted-component manifest, including any
   native adapter functions still covered by tests rather than source proofs.
5. Run one useful caller-supplied Python workflow and one shell workflow, including
   input use, bounded stdout/stderr, regular-file export and report retrieval.
   Add focused denial, cancellation/cleanup, storage-failure and lost-channel
   cases. Verify that returned reports and files belong to the requested run.
   Update the running guide and finish the scoped commits on `main`.

## Scope and proof boundary

The initial supported execution environment remains the designated disposable VM.
Use the published Linux/compiler/runtime assumptions in
[§FS-linux-product.trust](docs/functional-spec/FS-linux-product.md#trust-platform-assumptions-for-the-initial-product).
The application core's acceptance/filter/result properties must be checked for
its actual executable definitions. Full native control-path correspondence is
M5; selected kernel, binary-chain and hardware proofs are M6 improvements.
The historical M4 ledger keeps its original meaning and is not this task's exit
checklist. No record is relabeled as proved to deliver the product.

Linux source translation, a new recursor bridge, another compiler pipeline or an
alternative kernel are outside this assignment. Investigate an unfamiliar product
transport/build dependency early with an effort bound and a specific decision;
resolve it and continue the workflow. Surface a user decision only when needed,
with concrete options and a recommendation.

## Validation and handoff

Use [§AR-tooling.checks](docs/architecture/AR-tooling.md#checks-one-development-gate): focused checks while implementing, one final run
covering changed consumers, and matching-input reuse for unchanged proof evidence.
Run hostile workloads only in the disposable VM. A source/profile change needs
its affected VM cases and artifact bindings; documentation changes do not require
another full proof build. Preserve archived inputs at their recorded revisions.

The final handoff must give the working public commands, one reproducible caller
example, reusable library entry, bundle/trust manifest, actual proof bindings,
validation outcome and commit. Describe the delivered capability in plain language.
Continue until the acceptance contract is satisfied; supporting work remains
inside the assignment.
