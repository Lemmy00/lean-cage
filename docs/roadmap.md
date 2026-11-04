# RM-roadmap: LeanCage specification and staged verification plan

The destination is a reusable native Linux sandbox with end-to-end correctness,
isolation, and software-observable side-channel guarantees for named deployment
profiles: [§GOAL-end-to-end](goals.md#goal-end-to-end-connect-the-policy-to-the-deployed-artifact), [§GOAL-native-isolation](goals.md#goal-native-isolation-contain-arbitrary-native-workloads), and [§GOAL-confidentiality](goals.md#goal-confidentiality-account-for-software-observable-leakage).
Each milestone must leave reusable contracts and evidence for the next one.

**Planning revision: 2026-11-03.** The product contract is now
[§FS-linux-product](functional-spec/FS-linux-product.md#fs-linux-product-a-reusable-linux-workspace-with-an-explicit-trust-boundary), with the explicit trust decision
[§DA-product-assurance](decisions/architectural/DA-product-assurance.md#da-product-assurance-deliver-the-linux-product-with-explicit-platform-trust).
M1–M3 provide the tested offline workspace and reusable model/code proofs.
The reusable product was delivered at `92367a5`, reusing the output-capture
correction and source/compiler reporting connection reviewed at `fe96f16`.
The next delivery is the proved guest-entry interface under [§RM-roadmap.m5.next](roadmap.md#m5next-current-assignment).

This revision separates product delivery, complete application verification and
platform research. It does not mark the previous M4 contract complete. Earlier
milestone references and proof ledgers retain their historical meaning; the
[previous roadmap](https://github.com/Lemmy00/lean-cage/blob/fe96f1676f04907df8e398997fa6a9905e62c483/docs/roadmap.md)
preserves that scope. Current assignments use the revised acceptance contracts
below and [§FS-assurance.product](functional-spec/FS-assurance.md#product-product-assurance-levels-and-trusted-components).

## decisions: Accepted direction

- Implement a verified Lean replacement; use selected Bubblewrap behavior as the
  reference, not a requirement to certify its original C binary: [§DA-lean-linux](decisions/architectural/DA-lean-linux.md#da-lean-linux-build-a-lean-replacement-with-linux-as-the-first-backend).
- Use ordinary Lean theorem boundaries and Velvet where useful: [§AR-verification](architecture/AR-verification.md#ar-verification-compose-explicit-refinement-and-security-arguments).
- Make Linux the first backend. Consider seLe4n only after M3: [§DA-secondary-backend](decisions/architectural/DA-secondary-backend.md#da-secondary-backend-consider-sele4n-after-the-first-useful-linux-profile).
- Include timing, caches, contention, and speculation; exclude physical power/EM
  measurements and physical tampering: [§DF-security-scope](decisions/functional/DF-security-scope.md#df-security-scope-include-software-observable-hardware-channels-in-the-destination).
- Trial Grund only in this project, with pinned tooling and canonical linked
  documentation: [§DA-grund](decisions/architectural/DA-grund.md#da-grund-trial-pinned-grund-inside-this-repository-only).

## sequence: Delivery stages and dependencies

| Stage | Deliverable | Completion evidence |
|---|---|---|
| M0–M3, preserved | Existing specifications, filter/lifecycle proofs and offline VM workspace | Their accepted profile records remain inputs to the product |
| M4 | Reusable Linux product with verified executable policy/reporting core | Caller-supplied shell/Python runs through root build/check/run/report, reusable library, functional layout, exact core proof inventory and trusted component manifest |
| M5, planned | Complete application control-path verification in five named deliveries | Guest entry, host boundary, policy authority, owned lifetime and justified public observations compose under primitive platform contracts |
| M6 | Platform proofs, confidentiality and the seLe4n backend | Selected Linux/runtime assumptions are replaced by proofs; a named leakage property or a separate seLe4n execution profile is established |
| M7, starts after M4 | Supported releases and maintenance | Installable identified bundle, supported environment, update/recovery procedure, proof and test evidence matching its advertised claims |

M4 uses the existing Linux kernel and compiler/runtime as published trusted
components. M5 strengthens application guarantees. M6 research
is selected per profile and does not gate a functional release. A release that
advertises M5 or hardware guarantees must have that corresponding evidence.

## organization: Product consolidation at the next stable integration point

The M4 delivery implemented [§AR-product.organization](architecture/AR-product.md#organization-organize-the-maintained-product-by-responsibility): canonical functional source
paths, root build/run entry points and compatibility aliases preserving existing
proof/profile identities. Extend that structure. Milestone labels organize this
plan; new modules and scripts use functional names. Coordinate further necessary
migrations with active workers, and preserve historical evidence.

Every assignment must name a usable result, its existing consumer, and a concrete
acceptance check. Break large goals into integrated functional results. Lemmas,
test counts and repeated reviews are supporting work within those assignments.
Investigate uncertain dependencies early and revise the implementation route
when evidence calls for it; do not manufacture completion by replacing the
assigned result with an easier internal task.

## m0: Specification and development foundation

**Scope:** populate goals, specs, requirements, architecture, accepted decisions,
the compatibility matrix and assumption register; add a simple README and
development rules; pin Lean, Velvet and project-local Grund.

**Exit criteria:** `./scripts/check.sh` passes; Grund resolves the written
contracts and Lean comments; a deliberately dangling Lean citation fails in an
isolated fixture; the pinned Lean/Velvet library builds. The README and claim
register make the absence of runtime security results explicit.

**Reusable output:** stable IDs, proof/evidence rules, build/dependency locks, and
the next milestone's contract. No implementation of the future CLI is in scope.

## m1: First executable proof slice

Implement [§FS-filter-loading](functional-spec/FS-filter-loading.md#fs-filter-loading-prove-a-small-real-launch-boundary-first) using the pinned Bubblewrap source boundary.
Start with one explicit ABI and a small supported filter form. Specify byte and
integer semantics, architecture checks, validation, errors, and install-before-exec.

**Exit criteria:** kernel-checked decoder/bounds and launch-order theorems with
reviewed types and axiom sets; inhabited assumptions and success traces; explicit
OS/FFI contracts; isolated Linux demonstration of one allowed and one denied
action; malformed-input and failed-installation tests; a claim record distinguishing
the abstract proof from assumed kernel enforcement.

**Reusable output:** machine-level decoding, effect/failure interface, launch
state invariant, first concrete implementation/proof linkage, and evidence record.

## m2: Verified launcher lifecycle

**Status: M2.1–M2.7 complete for `linux-x86_64-root-helper-m2-v1`.** Evidence is
recorded in [the M2 handoff](reviews/M2-handoff.md) and [§FS-assurance.lifecycle](functional-spec/FS-assurance.md#lifecycle-m2-lifecycle-and-filter-semantics-claim-record).
Extend the real launch path under
[§FS-launch](functional-spec/FS-launch.md#fs-launch-establish-containment-before-executing-the-guest) and [§FS-isolation.process](functional-spec/FS-isolation.md#process-memory-and-process-boundaries). M1 starts inside a trusted child; M2 must
establish the supported entry conditions and supervise the resulting process tree.
The [M1 readiness review](reviews/M1-readiness.md) records the evidence and gaps.

### m2.boundary: Preserve the useful M1 result and expose the new obligations

Keep the fixed M1 decoder, exact-order proofs, and VM evidence as a regression
baseline. Define a richer state with owned resources, process identities,
credentials, signal state, and effect results. Relate its relevant successful
segment to M1's contract; a list of caller-supplied success events alone does not
establish that the executable performed those operations.

Select one concrete Linux x86-64 deployment profile before implementation:
launcher privileges, user/group and namespace setup, available kernel features,
trusted helper/runtime boundary, inherited resources, and supported cancellation
semantics. An unsupported environment fails preflight. Host administration and
hardware trust remain explicit; do not promise to defend against a malicious host
administrator merely by renaming M1's trusted entry assumptions.

The post-fork child currently executes C, outside the proved Lean transition
function. Decide how an executable controller or validated launch plan governs
that code, while keeping the child safe from inherited runtime/allocator state.
Record any manual native mapping as an open M4 correspondence obligation.

### m2.packages: Bounded work packages

| Package | Depends on | Required output and acceptance gate |
|---|---|---|
| M2.1 Lifecycle contract and execution design | Reviewed M1 | Map every M1 entry premise to establish, validate, reject, or retain-with-reason; define owned state, outcomes, and observations; select the supported privilege/helper profile; review the actual controller-to-native boundary before implementation |
| M2.2 Capable isolated test profile | M2.1 | A separately named, pinned kernel/configuration and guest image with the selected namespace, process, IPC and resource features; positive controls show the mechanisms exist; preserve the original M1 profile |
| M2.3 Owned resources and safe bootstrap | M2.1, M2.2 | Explicit descriptor allowlist/ownership, closed inherited authority, stable input/executable handles, argv/environment/cwd rules, and signal/thread bootstrap; cover short I/O and failures without guest entry |
| M2.4 Privilege and namespace transitions | M2.3 | Credential/group/capability and selected namespace setup with ordering, failure and inheritance contracts; prove the chosen launch invariant and test each boundary; setting no-new-privileges alone is insufficient |
| M2.5 Supervision, descendants and teardown | M2.3, M2.4 | Process ownership through fork/exec, reaping, parent death, signals, cancellation races and cleanup; typed results distinguish guest exit, setup failure and unknown supervision outcome; test pipe/report failure and descendant escape attempts |
| M2.6 Composition and filter semantics | M2.4, M2.5 | Compose the executable lifecycle with its effect contracts, preserve/refine the M1 theorem, and prove the fixed filter's action for arbitrary architecture/syscall inputs in a stated bytecode semantics; Linux correspondence stays separate |
| M2.7 Reviewed handoff | M2.2–M2.6 | Full statement/axiom audit, useful allowed workloads, adversarial failure/descendant fixtures, fresh VM evidence and exact artifact records; account for every remaining entry premise and M4 obligation |

The full M2 assignment proceeds through these packages in dependency order.
M2.1 produces concrete initial/post/failure-state contracts and a
source-to-effect map, including the point where guest execution becomes possible.
Do not move namespace contents or broad filesystem confinement into an informal
precondition; M2 owns setup/lifetime, and M3 owns the workspace authority policy.

### m2.gates: Exit criteria

A supported launch has a composed invariant across the real setup sequence and
all modeled failures. Inherited descriptors, credentials, signals, and descendants
must be dealt with explicitly. Cancellation is not considered complete until its
specified effect is observed; a missing error-pipe message is not proof of exec
success or of no guest entry. Termination/liveness claims state their scheduling
and OS premises separately from safety.

Tests must exercise supported mechanisms in an isolated VM, including inherited
handles, privileges, signal windows, existing-filter rejection/composition,
failed reporting, fork/exec, parent death, and cleanup of owned resources only.
A static native workload is sufficient for M2; general shell/Python runtime
support is an M3 gate. Publish the executable-to-model relationship honestly,
without importing M4's unproved native/Linux correspondence into a completion label.

**Reusable output:** owned-resource and lifecycle contracts, a compositional
launcher, an expanded test profile, and a precise M4 proof-obligation ledger.

## m3: Useful offline workspace sandbox

**Status: M3.1–M3.7 accepted for the conditional offline workspace profile.**
The full gate and fresh 60-case VM replay passed on 2026-10-31, including three
API checks and six death/cancellation boundaries. The [M3 review](reviews/M3-handoff.md) records delivery
and remaining assumptions. The profile supplies
[§FS-compatibility.matrix](functional-spec/FS-compatibility.md#matrix-initial-compatibility-matrix) for a real offline shell/Python workspace:
read-only runtime, private writable workspace, controlled I/O, confined
descendants, and explicitly supported resource limits.
The contract baseline is [§FS-workspace](functional-spec/FS-workspace.md#fs-workspace-m3-offline-workspace-contract-version-1) and [§AR-workspace](architecture/AR-workspace.md#ar-workspace-m3-authority-model-linux-realization-and-evidence-plan), with the runtime/policy
artifacts in `profiles/m3/`. Continue through the packages below in order; the
full milestone requires every acceptance gate.

### m3.packages: Build the profile in reviewable slices

| Package | Depends on | Required output and acceptance gate |
|---|---|---|
| M3.1 Authority and workload contract | M2.7 | Name runtime/workspace objects, allowed operations, protected host/sibling resources, public inputs, output disclosures, and descendant scope; pin one shell/Python runtime closure and policy format |
| M3.2 Filesystem realization | M3.1 | Root/mount/handle rules for read-only runtime and writable workspace; account for symlinks, hard links, rename/mount aliases, open handles, procfs and devices; no textual-prefix confinement argument |
| M3.3 Executable/runtime and filter policy | M3.1, M3.2, M2.6 | Support the selected dynamic loader/libraries/interpreters and fork/exec paths; separate private supervision results from arbitrary guest output before accepting these workloads; version the filter interface instead of weakening M1's exact nine-instruction acceptance; prove the supported policy-to-filter relation, with explicit Linux assumptions |
| M3.4 Offline and cross-process boundaries | M3.2, M3.3 | Constrain networking, IPC, tracing/signals and descriptor transfer; use isolated in-VM peers and positive controls so denial is caused by the chosen boundary, not absent kernel functionality |
| M3.5 Resource budgets and cancellation | M3.3, M2.5 | Precise memory/process/CPU/deadline semantics over descendants; selected cgroup/accounting/delegation and cleanup contracts; specified overshoot/failure behavior and no hidden fallback when mechanisms are unavailable |
| M3.6 Reusable interface and assurance report | M3.2–M3.5 | Library plus real check/run/report behavior over the private result transport, versioned policy and claim records, exact source/binary/platform identities, and truthful distinction between supported guarantees and remaining assumptions |
| M3.7 Acceptance and adversarial regression | M3.6 | Useful shell/Python workflows and confinement/limit/teardown tests, composed model proofs, fresh supported-profile evidence, and review of every residual Linux/runtime/hardware obligation |

### m3.gates: Acceptance is more than a successful Python invocation

Exercise filesystem races/aliases, inherited authority, fork/exec and orphaned
descendants, output/report failures, denied network/IPC, limits and cancellation.
Test useful permitted behavior alongside denial. The specification must state
which host interference is allowed; cooperating guest behavior is never a premise.

The M1/M2 static-ELF guards and deny-getppid filter are demonstration-specific.
Neither supplies the shell/Python runtime closure or workspace policy. M2 now has
a separate capable kernel with namespace, socket, IPC and cgroup positive controls.
Reuse that baseline where applicable, and version any kernel/configuration change;
feature presence alone is not evidence that an M3 boundary or limit is enforced.
Preserve the original M1 profile and evidence.

Keep resource mechanisms and scheduling premises explicit; a test timeout alone
does not establish a workload limit. Once implemented, the M3 profile may claim
its reviewed conditional model properties and tested native behavior. Full
application/platform correspondence and hardware-aware confidentiality follow
the revised M5/M6 tracks.

**Reusable output:** the first useful Linux workspace profile, stable authority
and backend contracts, and an evidence report. This remains the entry gate for
the optional M6 backend.

### m3.entry: M3.1 authority and workload contract

**Entry:** the reviewed M2 gate and source-bound VM evidence in
[the M2 handoff](reviews/M2-handoff.md). M3.1 is a contract/design package; it
does not implement M3.2–M3.7 or authorize deployment outside the disposable VM.

Write a versioned, most-specific workspace contract and architecture/decision
records implementing [§FS-policy.authority](functional-spec/FS-policy.md#authority-resources-and-permitted-operations),
[§FS-isolation.filesystem](functional-spec/FS-isolation.md#filesystem-object-level-confinement),
[§FS-isolation.interference](functional-spec/FS-isolation.md#interference-concurrency-and-environment),
[§FS-resources.limits](functional-spec/FS-resources.md#limits-precise-semantics), and
[§FS-observations.logical](functional-spec/FS-observations.md#logical-functional-observations). Deliver:

1. **Named profile and runtime.** Start from M2's root-helper/initial-user-namespace
   design. Pin one shell/Python runtime, loader, libraries and data closure with
   provenance/licenses. Specify useful offline workloads, unsupported requests,
   read-only runtime contents and writable workspace lifetime/export behavior.
2. **Object authority and interference.** Identify allowed objects/operations and
   protected host, supervisor and sibling resources. Cover aliases, existing
   descriptors, mounts, procfs/devices, executable replacement, concurrent host
   writers and guest-created descendants/threads. Do not infer sibling isolation
   from M2's shared UID 65534 or its public fixture tree.
3. **Launch and observation interfaces.** Define the minimal versioned policy and
   typed result, guest-entry knowledge, cleanup completion and cancellation races.
   Specify separate bounded guest I/O and private supervisor messages, including
   backpressure, forged guest output and failed/partial reports. Implement that
   private transport by M3.3; M3.6 completes the reusable public interface.
4. **Runtime and filter extension.** Explain dynamic loading/interpreter authority,
   executable identity and fork/exec inheritance. Introduce a distinct policy/filter
   contract; preserve M1's decoder and M2's sealed static profile as regressions.
5. **Resource contract.** State memory/process/CPU/deadline units, descendant scope,
   cgroup ownership/delegation, accounting/overshoot, OOM/limit outcomes and teardown.
   Keep trusted supervision outside guest-controlled limits and identify its own
   resource/liveness premises. A timeout is not a CPU or memory guarantee.
6. **Proof and correspondence plan.** State properties over actual object/effect
   transitions, useful witnesses and refinement to the M2 lifecycle. Extend
   [§AR-lifecycle.correspondence](architecture/AR-lifecycle.md#correspondence-m4-obligation-ledger) for loader, filesystem and resource effects.
   Name a concrete native-semantics route and a bounded first correspondence
   experiment, with criteria to replan if it cannot express the helper boundary.
   Tests/source maps remain evidence, not a substitute for that proof.
7. **Acceptance matrix and ownership.** Map every allowed/denied operation and
   failure/race to a theorem obligation or VM case. Include in-VM peers/positive
   controls, sibling/workspace interference, multithreaded fork/exec, cancellation,
   limits, result spoofing and moved-checkout evidence validation. Assign concrete
   files/interfaces to M3.2–M3.7 before implementation; preserve M1/M2 pins and gates.

The M3.1 artifacts are [§FS-workspace](functional-spec/FS-workspace.md#fs-workspace-m3-offline-workspace-contract-version-1), [§AR-workspace](architecture/AR-workspace.md#ar-workspace-m3-authority-model-linux-realization-and-evidence-plan), [§DA-m3-profile](decisions/architectural/DA-m3-profile.md#da-m3-profile-frozen-runtime-copied-workspace-and-distinct-run-authority), the
`profiles/m3/` runtime lock/policy schema/example and [acceptance matrix](reviews/M3-acceptance.md).
M3.2–M3.7 now supply the object/effect model, frozen runtime/workspace
construction, handle/alias rules, resource supervision, public interface and
evidence. Their precise model/test claims are [§FS-assurance.workspace](functional-spec/FS-assurance.md#workspace-m3-workspace-model-and-vm-evidence); this
original entry assignment is retained to explain the dependency boundary.

**Exit:** reviewed contract, decision record, runtime manifest, proof/assumption
ledger and executable-test plan; Grund formatting and the full repository gate
pass. Update the assurance register to distinguish these planned claims from the
completed M2 result. M3.2–M3.7 have separate implementation and acceptance gates;
the M3.1 contract alone does not complete workspace confinement.

## m4: Reusable Linux product and verified executable core

**Completed 2026-11-03 for the revised product contract.** The root build,
caller-policy VM workflow, Python/Lean libraries, functional source layout and
proof/trust bundle are delivered. The [product handoff](reviews/workspace-product-handoff.md)
and `assurance/product-vm-evidence.json` record acceptance and exact artifacts.

Implement [§FS-linux-product](functional-spec/FS-linux-product.md#fs-linux-product-a-reusable-linux-workspace-with-an-explicit-trust-boundary) using the existing controller, helper, runtime and
profile. Publish the Linux/runtime/compiler assumptions from the start. The
first supported environment remains the disposable VM; caller-supplied workloads
must work through a public interface without editing the acceptance harness.

**Exit:** the complete workflow in [§FS-linux-product.acceptance](functional-spec/FS-linux-product.md#acceptance-product-completion), with a reusable
library, functional source organization, documented root build, returned artifacts,
meaningful failure/cancellation handling and an inventory of proved properties
of the executable core. This is the revised product milestone, not acceptance of
the historical whole-platform verification contract.

### m4.packages: Integrated product deliveries

| Delivery | Existing implementation to reuse | Acceptance |
|---|---|---|
| Root build and functional source layout | Current Lake packages, CLI, native helper and runtime lock | One root build stages the actual controller/helper/profile; maintained product files are organized by responsibility; old proof/profile identities have an explicit migration map |
| Caller-policy VM workflow | `check`, `run`, `report` and the disposable VM tooling | A caller's policy/input snapshots produce its typed result, captures and permitted export; reject unsupported input and preserve safe cancellation/channel-loss behavior |
| Verified core and library interface | Executable policy/filter/decoder definitions and existing theorem inventory | Library and CLI call the same definitions; exact acceptance/bounds, emitted-filter behavior and live result equations are checked and linked to the bundle |
| Product acceptance | Existing VM cases, capture regression and proof gates | Useful Python and shell scenarios plus denial, cancellation, storage failure and lost-channel cases pass on the final changed inputs; unchanged proof evidence is reused |

These parts are integrated into the delivered workflow. Further application
verification consumes this implementation under [§RM-roadmap.m5](roadmap.md#m5-verify-the-complete-application-control-path); it does not
restart the completed product integration or accepted proof components.

### m4.next: Current M4 continuation

[M4-CONTINUE.md](../M4-CONTINUE.md) preserves the fulfilled assignment:
**a caller-supplied offline workspace is runnable through one root interface,
with reusable components and a declared trust boundary.** The
[product handoff](reviews/workspace-product-handoff.md) gives the working commands,
library entries, exact evidence and validation.
The current assignment is [§RM-roadmap.m5.next](roadmap.md#m5next-current-assignment); this stable historical section
remains available to existing citations.

Reuse the accepted parent/input work, the native output-capture correction,
[§AR-reporting.proof](architecture/AR-reporting.md#proof-check-the-interface-in-both-proof-environments) and [§AR-compiled-reporting.connection](architecture/AR-compiled-reporting.md#connection-carry-the-reporting-argument-across-verified-compilation).
The [compiler/reporting review](reviews/compiler-reporting-review.md) explains what
those results supply. The deeper compiler/runtime/kernel connections move to the
application/platform tracks below; they are not prerequisites for the root VM
workflow. Existing theorem statements and historical assurance records retain
their exact scopes.

### m4.entry: Next assignment — M4.1 native-semantics feasibility

**Historical contract, retained for existing citations and evidence.** New work
uses [§RM-roadmap.m4.next](roadmap.md#m4next-current-m4-continuation).

**Recorded feasibility outcome:** [M4.1 handoff](reviews/M4.1-handoff.md),
[§AR-m4-native.outcome](architecture/AR-m4-native.md#outcome-checked-pure-core-and-rejected-direct-effect-adapter) and the additive `assurance/m4-*` register.
The experiment is concluded with a negative direct-effect-route result and
checked codec subproofs; the unfinished universal native simulation is not marked
proved. [§AR-m4-native.revision](architecture/AR-m4-native.md#revision-byte-aware-effects-and-loss-before-the-lean-bridge) specifies the next route. The original assignment
below is retained as the acceptance contract.

**Entry:** M3 implementation `77a05d3` plus the reviewed report-storage correction
and plan on `main`, recorded in [the M3 main review](reviews/M3-main-review.md).
Read [§REQ-proof-integrity](requirements/REQ-proof-integrity.md#req-proof-integrity-never-substitute-a-weaker-claim-for-an-unfinished-proof), [§AR-workspace.experiment](architecture/AR-workspace.md#experiment-bounded-first-native-semantics-connection),
[§AR-workspace.correspondence](architecture/AR-workspace.md#correspondence-additional-open-m4-boundaries) and [§AR-lifecycle.correspondence](architecture/AR-lifecycle.md#correspondence-m4-obligation-ledger).
The existing CompCert 3.18 commit is the candidate semantics pin; exact compatible
Rocq/frontend/build pins and licensing must be recorded before use. Keep tools
project-local and retain the existing Lean/Velvet/Grund pins.

**Scope and ownership:** one worker owns `m4/`, `scripts/check_m4.sh`,
`assurance/m4-*`, a specific M4 architecture/decision record and
`docs/reviews/M4.1-handoff.md`. The roadmap and assurance register are shared
handoff files. Native extraction may touch `native/leancage_m3.c` and a small
shared header only when required to keep the experiment connected to the actual
helper; review that refactor and replay M3 before accepting it. No unrelated
workspace, global tool installation or production deployment is authorized.

Deliver the following in order:

1. **Exact slice and contract.** Select the live dispatcher/error/report-framing
   boundary promised in [§AR-workspace.experiment](architecture/AR-workspace.md#experiment-bounded-first-native-semantics-connection).
   Start from the actual `write_all`, little-endian codec, `send_frame`,
   `decode_frame` and terminal-error paths; identify precisely which functions
   and branches belong to the experiment and which remain outside it. Keep the
   300-authored-C-line bound using ordinary readable formatting. Include the
   real short-I/O/EINTR/error and invalid-tag paths; do not replace the helper
   with an unrelated idealized implementation. Record any necessary narrower
   extraction as a design decision with the excluded obligations still open.
2. **Reproducible semantics input.** Record source and preprocessed-source hashes,
   header/ABI definitions, exact extraction command, identified Clight AST and
   tool/source/license pins. Check mechanically that the proof input still
   comes from the maintained helper. Parser/frontend and extraction trust stay
   explicit unless independently discharged.
3. **Actual semantics proof attempt.** State and attempt the universal simulation
   from Clight execution to the selected operation/error/frame trace. Quantify
   over arbitrary input bytes and permitted effect outcomes; model owned buffer
   bounds, pointer arithmetic, machine widths and errno conversion. External
   call contracts may expose short transfers, interruption, EOF, failure and
   process loss; they must not assume containment or successful reporting.
   Prove memory safety/absence of undefined behavior for the claimed slice under
   explicit, inhabited ownership premises. Separate partial correctness from
   termination under repeated interruption or blocked external effects.
4. **Lean connection and claim ledger.** Identify the exact target declarations
   in M2/M3, especially result decoding and lifecycle knowledge. Record full
   proposition types and transitive assumptions in every proof assistant used.
   A Rocq proof plus a written mapping does not discharge the Lean connection;
   either check a bridge or leave that edge open for M4.2. The GCC binary,
   kernel effects and hardware remain open unless separately proved.
5. **Replay and decision.** Supply success, rejection, short-I/O/interruption and
   terminal-error witnesses plus tamper/stale-input checks. Add a bounded local
   `scripts/check_m4.sh`, then run Grund formatting, the full existing gate and
   the new gate. Run fresh VM/artifact checks if M3 source/evidence identities
   change. Publish commands, proof outputs, artifact hashes and residual gaps
   in the handoff, and update M4.2–6 based on evidence.

**Exit:** a reviewed feasibility result with an auditable connection to actual
source. If the candidate cannot model the slice faithfully, record the exact
reproducible obstruction and revised route instead of weakening the theorem or
marking native correspondence proved. An incomplete proof is explicitly
incomplete; a negative feasibility result can settle the tooling decision but
cannot count as a discharged security obligation. Full M4 remains open.

Keep completed work on `main`: start from its reviewed head, use a temporary
branch/worktree only if isolation is needed, then integrate passing, reviewed
commits back into `main` and push. Preserve other active work and never force-push.

## m5: Verify the complete application control path

**Status: planned; none of the five deliveries below is complete.** Establish
[§FS-linux-product.proofs.application](functional-spec/FS-linux-product.md#proofsapplication-the-complete-application-guarantee) across the host, VM init, Lean controller,
native helper and returned artifacts. M5 is a verification stage with separate
assignments, not one agent task. M4's elapsed time does not estimate this work:
M4 integrated a working implementation; M5 proves its application behavior.

| Delivery | Concrete guarantee and consumer | Dependencies and acceptance |
|---|---|---|
| M5.1 — Proved guest entry | The actual launch path reaches exec only with the required credentials, handles, filter and arguments; failure prevents entry. Consumed by the full authority/lifetime argument. | Start now. Settle the execution/proof route early; prove all entry/preflight paths and real caller connection under explicit prepared-run inputs. [§AR-application-verification.admission](architecture/AR-application-verification.md#admission-fail-closed-native-guest-admission) |
| M5.2 — Safe host boundary | Host snapshots and publication stay within owned paths and bounds for arbitrary VM output; accepted transport has consistent request/artifact identities. Consumed by every caller and later composition. | Independent of inner-VM correctness. Prove the executable decisions and their effect adapter; cover malformed bytes, unsafe paths and storage loss. [§AR-application-verification.host](architecture/AR-application-verification.md#host-safe-host-boundary-for-arbitrary-vm-output) |
| M5.3 — Policy-authorized setup | Caller bytes determine the actual argv, limits, snapshots, objects and run authority established before entry. Supplies M5.1's preparation premises. | Uses M5.1/M5.2. Prove byte interpretation, controller/VM handoff, native workspace construction and real argument/ownership producers. [§AR-application-verification.authority](architecture/AR-application-verification.md#authority-policy-authorized-workspace-construction) |
| M5.4 — Owned lifetime and limits | Supervision/cancellation targets only owned scopes, enforces the stated limits and justifies exit/cleanup observations across helper, VM and host. | Uses M5.3. Prove hostile interleavings and failure/loss safety; state progress assumptions separately. [§AR-application-verification.lifetime](architecture/AR-application-verification.md#lifetime-owned-descendants-limits-and-cancellation) |
| M5.5 — Justified public results | Each report field, capture and export follows from this run's observations; the whole public request composes under the named platform contracts. | Uses M5.1–M5.4; proves remaining sender/export/controller publication paths and discharges application premises at actual callers. [§AR-application-verification.composition](architecture/AR-application-verification.md#composition-justified-observations-and-the-complete-public-request) |

The preferred implementation direction is shared executable Lean control and
security decisions with small primitive adapters. The entry assignment must
resolve Lean runtime/fork constraints and any remaining native proof connection
before expanding the approach. Existing source proofs are reused where their
interfaces fit; rewriting a live path must preserve its public behavior and
archive the old evidence, not create a second implementation.

M5.2 can proceed independently after its own host-adapter route is concrete;
parallel ownership requires a separate assignment. Each delivery includes its
supporting lemmas, caller integration and one affected acceptance gate. Useful
component contracts may retain explicit premises that another named delivery
produces; no whole application component can remain an assumed secure operation
in M5.5. Neither test counts nor additional proof wrappers constitute completion.

**Exit:** the composed application theorem, inhabited requests, audited
transitive assumptions and bindings to the code in the identified bundle.
Compiler/runtime, precise primitive Linux behavior and the declared platform
remain assumptions. Their implementation proofs are M6 work. Estimate subsequent
deliveries after M5.1 demonstrates the approach on actual effectful code; the plan
does not promise that all five have equal difficulty or fit one session.

### m5.next: Current assignment

Deliver **M5.1 — proved guest entry**, using the full contract and execution
instructions in [§AR-application-verification.next](architecture/AR-application-verification.md#next-first-assignment-and-early-route-decision) and the value-carrying target
in [§FS-linux-product.proofs.entry](functional-spec/FS-linux-product.md#proofsentry-establish-actual-state-at-workload-entry). Preserve the working product at `92367a5` and
reuse its matching-input validation evidence.

The first four working hours bound the architecture investigation, not the
complete assignment. Demonstrate an actual caller-to-entry/failure path and its
checked proof connection, choose the implementation route, then finish the
complete entry interface, integration and acceptance. A failed prototype must
change the approach; it is not a substitute delivery. The host, authority,
lifetime and observation assignments remain explicit next work.

## m6: Platform trust reduction and confidentiality research

Assign a particular improvement to a product profile, with its consumer and a
bounded feasibility decision. Candidate tracks are:

- Supply the physical runtime/TLS/caller producers and connect verified compiler
  output to the deployed artifact where that improves the selected profile.
- Establish finite stack budgets and justified resource-exhaustion behavior under
  [§RM-roadmap.m6.resources](roadmap.md#m6resources-finite-stack-budgets-and-resource-exhaustion), starting with the trusted guest-entry path.
- Prove a selected Linux effect implementation against its published contract,
  including the relevant concurrency, errors and transitive dependencies.
- Establish the hardware-aware observation/leakage property in
  [§FS-observations.hardware](functional-spec/FS-observations.md#hardware-software-observable-channels) for a named CPU/kernel/configuration.
- Deliver the separate seLe4n backend track in [§RM-roadmap.m6.sele4n](roadmap.md#m6sele4n-a-sele4n-backend-using-the-same-portable-contracts).

These are independent assignments, not a single "finish M6" task. Choose one
named assumption/property and its product consumer. If an M5 route change moves
control from C to Lean, update the binary-chain target to the code actually
shipped, including Lean compiler/runtime trust; preserve earlier CompCert results
at their recorded source boundary. Do not translate the whole kernel as an entry
requirement for an application proof.

**Exit for an assigned upgrade:** the replacement producer or leakage theorem is
consumed by the profile's composed argument, and the profile's trusted-component
record is updated accordingly. Preserve the broader end-to-end destination.
There is no requirement to complete every research track before releasing a
useful Linux product. A hardware-confidentiality claim requires its own completed
observation and mechanism proof.

### m6.resources: Finite stack budgets and resource exhaustion

**Status: planned follow-on after the M5 entry route stabilizes.** This is a named
M6 assurance upgrade under [§FS-resources.limits](functional-spec/FS-resources.md#limits-precise-semantics) and [§FS-resources.availability](functional-spec/FS-resources.md#availability-restricted-availability-claims).
The active M5 assignments keep their existing acceptance contracts. This track
supplies a resource-availability premise for their deployed application argument;
it applies to the C, Lean and runtime code actually selected by M5.

**Reason:** the CompCert memory model used through Rocq has a total `Mem.alloc`
operation without a finite total-memory budget. In the pinned source recorded
by `m4/toolchain-lock.json`, Clight `alloc_variables` and x86 assembly-model
`Pallocframe` use it. The [upstream memory documentation](https://compcert.org/doc/html/compcert.common.Memory.html)
states this allocation abstraction explicitly. Existing source/assembly-model
proofs therefore do not by themselves establish that a real process has enough
stack. This is a semantics/deployment boundary, not a defect of Rocq's logic.
Guest cgroup memory limits also do not establish the trusted controller/helper's
own stack budget.

**First delivery:** give the supported profile a checked usable-stack requirement
for its actual guest-entry path, including the caller and transitive callees.
Consume the M5.1 entry guarantee under that proved budget and tie the requirement
to the shipped executable/runtime configuration. The before/after is an explicit
available-stack premise becoming a justified admission condition for this path.
Record the runtime, ABI, process/thread and interference assumptions that remain.

Deliver the following within that assignment:

1. **Account for real stack use.** Establish maximum simultaneously live stack
   bytes, including caller frames, recursion, local arrays, alignment, saved
   registers/spills, runtime/libc/FFI calls and any permitted signal/callback
   frames. Account for usable mapped space, guards and required reserves. Source
   call depth alone is insufficient; compilation can change frame sizes. Use a
   checked conservative bound through compilation or validated binary costs;
   compiler reports and measurements may propose bounds but do not prove them.
2. **Distinguish stack space from fuel.** A stack budget is charged on entry and
   released on return. Execution-step fuel bounds work and need not track peak
   stack use. Fuel is an optional technique: if used, define what consumes it,
   connect it to the executed program, prove adequacy and cover exhaustion.
   Checking one chosen fuel value is only bounded evidence. General safety needs
   a proof for all relevant prefixes or a proved/enforced input-derived bound.
   Retain the separate scheduler/primitive-progress assumptions for liveness.
3. **Connect finite execution and failure.** Prove the selected resource-aware
   semantics agrees with the existing application semantics while budgets
   suffice. Prove admitted executions fit the available stack; reject an
   insufficient configuration before guest entry. Include allocation/worker-loss
   outcomes where the platform permits them. Preserve justified observations
   through an independently resourced supervisor or another proved mechanism;
   do not assume an exhausted stack can execute its own cleanup/reporting code,
   or represent exhaustion merely by deleting the failing transition.
4. **Integrate and validate.** Publish the bound, input restrictions, binary and
   runtime identities, checked theorem/assumptions and the platform admission
   check. Show a useful admitted execution and insufficient-budget/failure
   behavior in the disposable VM, with no forged entry or cleanup success.
   Verify safe handling before claiming that an actual stack overflow behaves
   like the existing process-loss abstraction.

**Exit:** the identified guest-entry path consumes a checked finite-stack bound
and its real admission/failure behavior satisfies the application contract.
Expand afterward through separately assigned trusted supervision/reporting paths
and heap/allocation budgets. State exactly which paths are covered; a finite
stack result for one helper is not a whole-runtime memory or availability theorem.
Any release advertising finite-resource guarantees must consume the corresponding
completed evidence under [§RM-roadmap.m7](roadmap.md#m7-supported-releases-and-maintenance).

### m6.sele4n: A seLe4n backend using the same portable contracts

seLe4n remains a named planned backend under
[§DA-secondary-backend](decisions/architectural/DA-secondary-backend.md#da-secondary-backend-consider-sele4n-after-the-first-useful-linux-profile).
It can start independently of the Linux application/platform proofs after the
accepted M3 baseline. M4's component consolidation supplies a cleaner shared
interface; finishing Linux implementation verification is not an entry requirement.

The first delivery is a bounded native-workload execution profile that consumes
the shared policy, authority and result interfaces. It must admit a useful allowed
workload, reject an unauthorized operation, return bounded output and report its
termination/cleanup. Select and publish its supported workload/ABI explicitly;
do not assume the Linux shell/Python runtime is portable without additional work.

Investigate the pinned kernel's actual boot, userspace, compiler/runtime and
binding path first, with a bounded route decision. Then implement the capability
adapter and connect its operations to the shared confinement and observation
contracts. Acceptance requires a runnable isolated demonstration, a checked
backend refinement for the advertised subset, and its own deployment/trust record.
A kernel-model adapter alone is an intermediate result. If execution support is
missing, identify and implement the needed integration, or present the concrete
architecture decision that is needed to proceed.

Boot/toolchain feasibility can start now. Before assigning backend refinement,
agree the value-carrying entry and observation interfaces used by
[§AR-application-verification.admission](architecture/AR-application-verification.md#admission-fail-closed-native-guest-admission) and [§AR-application-verification.composition](architecture/AR-application-verification.md#composition-justified-observations-and-the-complete-public-request).
The existing label-level lifecycle model alone is not the backend's execution
contract; Linux-specific mechanisms stay in their adapter.

## m7: Supported releases and maintenance

Begin release engineering after the M4 product gate. Release identified bundles
whose exact claims meet [§FS-assurance.product](functional-spec/FS-assurance.md#product-product-assurance-levels-and-trusted-components) and [§FS-assurance.closure](functional-spec/FS-assurance.md#closure-rules-for-stronger-claims).
An initial release can advertise the tested Linux profile and its verified core;
a later release can add M5 application verification or selected M6 upgrades.

**Exit:** reproducible package and documented installation/run API, supported
platform preflight, regression coverage, proof/evidence manifest, licenses,
update/revalidation policy, recovery/quarantine behavior and a security-reporting
process. Keep the first supported execution environment explicit; extending from
VM execution to direct deployment requires a separate platform contract and tests.
Only the claims actually advertised determine the required assurance upgrades.
The experimental/core profile can ship before M5. Stabilize any changed
execution/proof route before freezing a stronger supported bundle; changing
source language or a trusted component requires a new identified evidence set.

## next: M1 work packages and next scope

**M1.1–M1.5 are complete for the stated M1 scope.** M1.1's evidence is the pinned source map,
ABI/filter table, launch/failure contracts, and 14 reference-fixture checks in
[§AR-filter-slice](architecture/AR-filter-slice.md#ar-filter-slice-m11-source-map-and-typed-contract-boundary). M1.2 adds the executable pure decoder, exact acceptance,
bounds/first-error proofs, a successful snapshot witness, malformed-input tests,
and the auditable claim record [§FS-assurance.decoder](functional-spec/FS-assurance.md#decoder-m12-decoder-claim-record). The full `./scripts/check.sh`
gate is required at handoff. These prove the stated decoder property only.

M1.3 adds all specified success/failure/interference transitions, exact ordered
launch histories, terminal failures, actual decoder linkage, and inhabited
success/failure traces under [§FS-assurance.launch](functional-spec/FS-assurance.md#launch-m13-launch-order-claim-record). M1.4 supplies the original
native driver and isolated Linux demonstration in [§FS-assurance.demo](functional-spec/FS-assurance.md#demo-m14-isolated-linux-test-record). M1.5
preserves the original decoder theorem types/axioms, extends the audit, and
records assumptions and validation. These establish M1's limited functional
proof slice, not full isolation or certified native/Linux correspondence.

| Work package | Depends on | Concrete output and review gate |
|---|---|---|
| M1.1 Source and contract slice | M0 | Implemented: [§AR-filter-slice](architecture/AR-filter-slice.md#ar-filter-slice-m11-source-map-and-typed-contract-boundary); reviewed pinned source and typed contracts; no security theorem |
| M1.2 Decoder and bounds | M1.1 | Implemented: [§AR-filter-decoder](architecture/AR-filter-decoder.md#ar-filter-decoder-byte-decoder-proofs-and-executable-evidence-audit), with evidence under [§FS-assurance.decoder](functional-spec/FS-assurance.md#decoder-m12-decoder-claim-record); pure decoder claim only |
| M1.3 Launch transition proof | M1.1 | Implemented: [§AR-m1-launch.model](architecture/AR-m1-launch.md#model-total-transitions-and-trace-evidence); 25 added authored theorems, exact order, nonvacuity and decoder linkage |
| M1.4 Linux binding and demonstration | M1.2, M1.3 | Implemented: [§AR-m1-launch.binding](architecture/AR-m1-launch.md#binding-small-native-boundary) and [§AR-m1-launch.vm](architecture/AR-m1-launch.md#vm-disposable-linux-profile-and-evidence); all 13 VM cases pass, including a fresh source/kernel build |
| M1.5 Claim review and handoff | M1.4 | Passed `./scripts/check.sh`: 21 Python tests, 58 Lean guards, native build, full type/axiom audit; 43 authored claims and 445 total theorem declarations, 39 source/dependency/evidence hashes; original decoder baseline preserved |

The handoff gate and explicit VM replay both passed on 2026-10-30. The proof gate
rejects custom/unfinished/compiler-trust axioms; the audited union remains only
the three declared logical foundations. [§FS-assurance.launch](functional-spec/FS-assurance.md#launch-m13-launch-order-claim-record) and
[§FS-assurance.demo](functional-spec/FS-assurance.md#demo-m14-isolated-linux-test-record) record the proof/test boundary and remaining assumptions.

M2 extends this preserved baseline with [§FS-lifecycle](functional-spec/FS-lifecycle.md#fs-lifecycle-m2-owned-launcher-lifecycle) and [§AR-lifecycle](architecture/AR-lifecycle.md#ar-lifecycle-m2-controller-native-helper-and-evidence). The
full M2 implementation is reviewed in [the M2 handoff](reviews/M2-handoff.md).
The subsequent M3 packages are documented in [§RM-roadmap.m3.packages](roadmap.md#m3packages-build-the-profile-in-reviewable-slices) and the
[M3 handoff](reviews/M3-handoff.md). After that gate, start the bounded first M4
experiment in [§AR-workspace.experiment](architecture/AR-workspace.md#experiment-bounded-first-native-semantics-connection). The earlier M2 entry assignment was
**M2.1: lifecycle contract and execution design** in
[§RM-roadmap.m2.packages](roadmap.md#m2packages-bounded-work-packages). Read the [M1 review](reviews/M1-readiness.md) and
[§FS-filter-loading.installation.entry](functional-spec/FS-filter-loading.md#installationentry-entry-conditions-and-interference), inventory every trusted entry condition,
then propose the concrete state/effect/ownership and native execution boundary.
Its acceptance gate is a reviewed contract and test-profile plan. M2.2–M2.6 now
supply the selected profile, native helper, lifecycle/bytecode proofs and VM
regressions. M2.7 passed the full gate, statement/axiom audit and 43-case fresh VM replay. The
M1 proofs and raw evidence remain preserved.

Each assignment must state the spec IDs, owned files, intended theorem or behavior,
assumptions, validation commands, and completion evidence. Shared-interface changes
need coordination before parallel implementation. Follow [agent rules](../AGENTS.md).

## validation: Validation across milestones

Select checks and reuse matching-input results under [§AR-tooling.checks](architecture/AR-tooling.md#checks-one-development-gate).
Code/proof handoffs require the foundation and affected package gates once on the
final relevant inputs; prose-only handoffs use documentation checks. An aggregate
counts for its included prerequisites. As behavior appears, add targeted tests
for malformed policies/filters, architecture mismatches, setup failures, descriptor
leaks, symlink/rename races, privilege changes, fork/exec, cancellation, and limits.
Use pinned differential tests for compatibility and tests of allowed behavior as
well as denial. Audit theorem statements, transitive axioms, nonvacuity, and artifact
bindings. Neither tests nor document coverage replace proofs.
