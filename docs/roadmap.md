# RM-roadmap: LeanCage specification and staged verification plan

The destination is a reusable native Linux sandbox with end-to-end correctness,
isolation, and software-observable side-channel guarantees for named deployment
profiles: [§GOAL-end-to-end](goals.md#goal-end-to-end-connect-the-policy-to-the-deployed-artifact), [§GOAL-native-isolation](goals.md#goal-native-isolation-contain-arbitrary-native-workloads), and [§GOAL-confidentiality](goals.md#goal-confidentiality-account-for-software-observable-leakage).
Each milestone must leave reusable contracts and evidence for the next one.

**Current stage: M1–M3 accepted for their stated conditional profiles.**
The [M3 handoff](reviews/M3-handoff.md) records the useful offline workspace,
checked model claims and fresh VM evidence. The bounded M4.1 experiment now
records checked pure-codec executions and a rejected direct I/O-effect adapter;
its full native simulation remains unproved (see [the M4.1 handoff](reviews/M4.1-handoff.md)).
The source/ABI slice, pure decoder/bounds proofs, exact launch-order proofs,
native Linux driver, and 13-case isolated VM demonstration are recorded under
[§AR-filter-slice](architecture/AR-filter-slice.md#ar-filter-slice-m11-source-map-and-typed-contract-boundary), [§AR-filter-decoder](architecture/AR-filter-decoder.md#ar-filter-decoder-byte-decoder-proofs-and-executable-evidence-audit), and [§AR-m1-launch](architecture/AR-m1-launch.md#ar-m1-launch-launch-model-linux-driver-and-isolated-demonstration). The claim register
[§FS-assurance.status](functional-spec/FS-assurance.md#status-initial-claim-register) separates model proofs, VM tests, and remaining
native/Linux correspondence assumptions. Full confinement and hardware-channel
security remain later milestones. The [independent M1 readiness review](reviews/M1-readiness.md)
accepts this limited scope and defines the M2/M3 planning changes below.

## decisions: Accepted direction

- Implement a verified Lean replacement; use selected Bubblewrap behavior as the
  reference, not a requirement to certify its original C binary: [§DA-lean-linux](decisions/architectural/DA-lean-linux.md#da-lean-linux-build-a-lean-replacement-with-linux-as-the-first-backend).
- Use ordinary Lean theorem boundaries and Velvet where useful: [§AR-verification](architecture/AR-verification.md#ar-verification-compose-explicit-refinement-and-security-arguments).
- Make Linux the first backend. Consider seLe4n only after M3: [§DA-secondary-backend](decisions/architectural/DA-secondary-backend.md#da-secondary-backend-consider-sele4n-after-the-first-useful-linux-profile).
- Include timing, caches, contention, and speculation; exclude physical power/EM
  measurements and physical tampering: [§DF-security-scope](decisions/functional/DF-security-scope.md#df-security-scope-include-software-observable-hardware-channels-in-the-destination).
- Trial Grund only in this project, with pinned tooling and canonical linked
  documentation: [§DA-grund](decisions/architectural/DA-grund.md#da-grund-trial-pinned-grund-inside-this-repository-only).

## sequence: Milestones and dependencies

| Milestone | Entry dependency | Deliverable | Assurance boundary |
|---|---|---|---|
| M0 | Project decisions | Specification, rules, pinned tooling/build | No runtime security claim |
| M1 | M0 | Executable filter/launch proof slice | Abstract proof; Linux enforcement assumed |
| M2 | M1 | Verified launcher lifecycle | OS contracts and binary correspondence still explicit |
| M3 | M2 | Useful offline workspace sandbox | Native workloads; remaining Linux/runtime/hardware gaps listed |
| M4 | M3, with contract research from M1 | Linux and executable correspondence | Relevant code and transitive dependencies connected |
| M5 | Observer requirements from M0; deployed closure needs M4 | Hardware-aware isolation for a named profile | Hardware model fidelity remains explicit |
| M6 | M3 | Optional seLe4n backend | Separate proof chain; can proceed alongside M4/M5 |
| M7 | M4 and M5 for the advertised Linux profile | Supported production releases | Complete advertised chain and published foundational assumptions |

M4 and M5 are substantial research programs, with no promised completion date.
Their interfaces must influence early work. If a proposed guarantee is infeasible
on a profile, document that result and investigate a suitable restricted profile;
do not silently weaken the contract or count an assumption as a discharged proof.

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
executable/Linux correspondence and hardware-aware confidentiality remain M4/M5.

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

## m4: Linux and executable correspondence

Close the gap from Lean semantics to the actual executable and Linux enforcement
under [§AR-linux.correspondence](architecture/AR-linux.md#correspondence-reduce-the-linux-assumption) and [§AR-verification.artifacts](architecture/AR-verification.md#artifacts-bind-proofs-to-releases). Cover compilation,
native runtime, loader, foreign bindings, ABI, relevant Linux code and its transitive
dependencies, for a fixed kernel configuration.

Start the correspondence work during M2: inventory the C/FFI/runtime operations,
choose the semantics and first concrete boundary to connect, and record which
launch invariant each obligation supports. Each new M2/M3 feature must extend
that ledger. Do not wait for a large launcher to accumulate before testing
whether its implementation can be related to the model.

**Exit criteria:** an explicit refinement chain for the advertised properties;
identified executable and kernel artifacts; all relevant obligations either
discharged or visible as remaining limitations that prevent the stronger claim.
Manual code maps and differential tests cannot substitute for a correspondence
proof. Avoid claiming the entire kernel has been verified.

**Reusable output:** semantics, proof connections, and reproducible artifact
evidence that can support more features and maintained Linux profiles.

### m4.packages: Correspondence work after the reviewed M3 baseline

M4 is a research program, not one agent-sized implementation task. M4.1's
bounded feasibility result is recorded in [the handoff](reviews/M4.1-handoff.md)
and [§AR-m4-native.outcome](architecture/AR-m4-native.md#outcome-checked-pure-core-and-rejected-direct-effect-adapter). The direct silent/count-only effect route is rejected;
the full simulation, whole-slice memory safety and checked Lean bridge are
unproved. The [continuation record](reviews/M4-progress.md) adds a checked byte-aware
effect/loss layer and Lean endpoint lemmas under [§AR-m4-effects](architecture/AR-m4-effects.md#ar-m4-effects-byte-aware-native-effects-and-asynchronous-loss). The [write-loop review](reviews/M4-writeall.md)
completes a source submilestone under [§AR-m4-effects.writeall](architecture/AR-m4-effects.md#writeall-universal-source-loop-connection): universal finite-execution
prefix safety, defined execution and exact returns for the maintained `write_all`,
with arbitrary retry/wait/loss witnesses. The [reporting-primitives review](reviews/M4-primitives.md)
adds universal source-prefix safety, exact returns and bounded execution for
`error_number`, `get32` and `get64` under [§AR-m4-effects.errno](architecture/AR-m4-effects.md#errno-source-errno-normalization-and-bounded-execution) and
[§AR-m4-effects.readers](architecture/AR-m4-effects.md#readers-universal-bounded-frame-reader-execution), with arbitrary caller continuations in the constructive
paths and allocated arbitrary-value witnesses. The [writer review](reviews/M4-writers.md)
adds every-prefix byte-store safety, unchanged outside memory/permissions,
42/74-step source bounds, loss after the first store, and exact source codec
round trips under [§AR-m4-effects.writers](architecture/AR-m4-effects.md#writers-byte-stores-and-source-codec-round-trips). The [library review](reviews/M4-library.md) adds local comparison/copy/close/exit contracts,
universal preservation of earlier source proofs in the extended machine, and the
complete `fault` source connection under [§AR-m4-library.source](architecture/AR-m4-library.md#source-source-connections-and-completion-boundary). The [structure review](reviews/M4-structures.md) adds complete `result_of` source
execution, typed local allocation/stores/copy/free, exact fields, outside-memory
preservation and every-prefix loss under [§AR-m4-structures.result](architecture/AR-m4-structures.md#result-complete-result-constructor). The [caller review](reviews/M4-callers.md) adds bidirectional actual call
composition and the complete `fail_child` source: every-prefix ordinary progress,
exact reporting prefixes, non-return, exit code 125 and owned success/drop/short/
failed/lost executions under [§AR-m4-callers.failure](architecture/AR-m4-callers.md#failure-complete-child-failure-reporting). The [decoder review](reviews/M4-decoder.md) adds the complete `decode_frame` source from arbitrary owned 160-byte frames: exact header/payload/tag acceptance, early versus late rejection mutation, ordinary progress at every finite live prefix, outside-memory preservation and actual local free under [§AR-m4-decoder](architecture/AR-m4-decoder.md#ar-m4-decoder-complete-private-frame-decoding-from-owned-bytes). Its replay also repairs the historical caller import closure without changing preceding claims. The [sender/finish review](reviews/M4-sender.md) adds complete frame construction,
ordered fault checks, exact publication results and actual frees, plus `finish`
execution through both successful and failed publication under [§AR-m4-sender](architecture/AR-m4-sender.md#ar-m4-sender-complete-frame-sending-and-publication-return-behavior).
The [receiver review](reviews/M4-receiver.md) adds the complete terminal-error read
loop, exact classification from its actual read trace, ignored close failure,
all copies/frees and allocated retry/error/loss executions under [§AR-m4-receiver](architecture/AR-m4-receiver.md#ar-m4-receiver-complete-terminal-error-receiver-from-owned-inputs).
The [report-byte review](reviews/M4-wire.md) connects actual sender/decoder and
child/receiver histories through exact observed bytes, with private acceptance,
rejection mutation and allocated execution pairs under [§AR-m4-wire](architecture/AR-m4-wire.md#ar-m4-wire-source-connections-through-exact-report-bytes).
These are partial M4.2 results; the remaining selected-slice simulation and checked bridge remain open. M4.3–M4.6
remain planned, and none of these additions completes M4.

| Package | Dependency | Deliverable and gate |
|---|---|---|
| M4.1 Native-semantics feasibility | Reviewed M3 on `main` | Feasibility result recorded: 260-line maintained-source extraction, checked pure-reader executions, and refuted direct effect adapters; full reporting simulation unproved |
| M4.2 Checked connection to Lean | M4.1 revised effect route | Byte-aware effects, asynchronous loss and exact Lean endpoints checked; local `write_all` source safety plus universal errno/frame-reader safety, exact returns and bounded execution checked under [§AR-m4-effects.writeall](architecture/AR-m4-effects.md#writeall-universal-source-loop-connection), [§AR-m4-effects.errno](architecture/AR-m4-effects.md#errno-source-errno-normalization-and-bounded-execution) and [§AR-m4-effects.readers](architecture/AR-m4-effects.md#readers-universal-bounded-frame-reader-execution); byte writers and exact source codec round trips checked under [§AR-m4-effects.writers](architecture/AR-m4-effects.md#writers-byte-stores-and-source-codec-round-trips); local library effects and the complete `fault` source selector checked under [§AR-m4-library.source](architecture/AR-m4-library.md#source-source-connections-and-completion-boundary); complete `result_of` construction and local storage checked under [§AR-m4-structures.result](architecture/AR-m4-structures.md#result-complete-result-constructor); actual caller composition and complete `fail_child` source checked under [§AR-m4-callers.failure](architecture/AR-m4-callers.md#failure-complete-child-failure-reporting); complete private-frame decoding and rejection mutation checked under [§AR-m4-decoder.source](architecture/AR-m4-decoder.md#source-actual-construction-and-validation); complete frame sending and `finish` publication/exit mapping checked under [§AR-m4-sender.reporting](architecture/AR-m4-sender.md#reporting-source-fault-checks-and-complete-writes) and [§AR-m4-sender.finish](architecture/AR-m4-sender.md#finish-exit-mapping-despite-publication-failure); complete terminal receiver, actual read-trace classification, nine-byte bound and local frees checked under [§AR-m4-receiver](architecture/AR-m4-receiver.md#ar-m4-receiver-complete-terminal-error-receiver-from-owned-inputs); exact sender/decoder and child/receiver observation connections checked under [§AR-m4-wire](architecture/AR-m4-wire.md#ar-m4-wire-source-connections-through-exact-report-bytes); whole-program ordering, Linux byte provenance, valid wait-status provenance and C-to-Lean bridge still open |
| M4.3 Controller and helper composition | M4.1–2 | Expand through parser/plan, memory/ABI, operation ordering, errors, asynchronous reports, supervision and cleanup; every local external effect gets a byte/memory/error contract and source connection; preserve partial decoder mutation and failed publication facts |
| M4.4 Pinned Linux enforcement | Effect contracts from M4.3; research may overlap | Discharge the relevant VFS/mount/descriptor, process/credential, seccomp and cgroup obligations against the pinned kernel and transitive dependencies; track each original M2/M3 ledger entry separately, including the byte-aware I/O/errno contract and loss/progress premises exposed by M4.1 |
| M4.5 Executable and runtime chain | M4.2–4 interfaces; artifact work may overlap | Connect compiler output, linking, Lean/native runtimes, loaders, runtime closure, kernel and deployed artifacts; review the actual assigned CompCert commit (VERSION 3.17 despite the earlier 3.18 label), licensing and any altered event semantics before applying compiler theorems; hashes alone do not prove correctness |
| M4.6 Composed profile review | M4.3–5 | Compose the advertised functional properties for a named deployment profile, replay independently, and account for every remaining assumption; the M4.1 negative adapter result discharges no native security obligation; open correspondence gaps prevent a full M4 completion claim |

M5 retains timing/cache/contention/speculation work. M6 remains optional. Neither
is a shortcut around the Linux/executable obligations or a reason to expand the
VM profile while its correspondence is still unproved.

### m4.entry: Next assignment — M4.1 native-semantics feasibility

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

## m5: Hardware-aware isolation

Fulfill [§FS-observations.hardware](functional-spec/FS-observations.md#hardware-software-observable-channels) for a named CPU/kernel/configuration profile.
Develop the observer model from M0 onward; investigate mechanisms such as resource
partitioning, scheduling controls, and restrictions only as justified by that model.
M2 must identify public launch/failure observations; M3 must identify workspace
secrets and authorized output. These are inputs to the later hardware-aware
argument, not early timing-confidentiality claims.

**Exit criteria:** explicit timing/cache/contention/speculation observations and
attacker powers; security theorem for the stated leakage property; connection to
the deployed mechanisms and M4 chain; useful workload witnesses; supplemental
leakage experiments; published hardware-model fidelity assumptions.

**Reusable output:** hardware-aware observation/refinement interfaces and supported
profile evidence. VM tests alone cannot establish this milestone.

## m6: Optional second backend

After M3, evaluate the seLe4n track in [§DA-secondary-backend](decisions/architectural/DA-secondary-backend.md#da-secondary-backend-consider-sele4n-after-the-first-useful-linux-profile). Check toolchain and
license compatibility before adding dependencies, and reuse the portable contracts.

**Exit criteria:** a separate backend refinement to the chosen kernel model;
audited trusted hardware contracts, runtime and bindings; a useful workload and
a separate evidence record. This does not discharge Linux obligations.

## m7: Supported production releases

Release identified, reproducible artifacts for profiles whose advertised claims
meet [§FS-assurance.closure](functional-spec/FS-assurance.md#closure-rules-for-stronger-claims). Publish supported policies/workloads, theorem and
artifact evidence, residual foundational assumptions, operational prerequisites,
and update/revalidation procedures.

**Exit criteria:** independent replay of proof checks and reproducible artifact
identification; no open obligation concealed inside a claimed guarantee; supported
deployment procedure and regression process. Broaden platforms/features only with
new or preserved contracts and evidence. M6 is required only for a claimed seLe4n
release, not for a Linux release.

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

Run the foundation checks on every handoff. As behavior appears, add targeted tests
for malformed policies/filters, architecture mismatches, setup failures, descriptor
leaks, symlink/rename races, privilege changes, fork/exec, cancellation, and limits.
Use pinned differential tests for compatibility and tests of allowed behavior as
well as denial. Audit theorem statements, transitive axioms, nonvacuity, and artifact
bindings. Neither tests nor document coverage replace proofs.
