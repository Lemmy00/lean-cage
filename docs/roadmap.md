# RM-roadmap: LeanCage specification and staged verification plan

The destination is a reusable native Linux sandbox with end-to-end correctness,
isolation, and software-observable side-channel guarantees for named deployment
profiles: [§GOAL-end-to-end](goals.md#goal-end-to-end-connect-the-policy-to-the-deployed-artifact), [§GOAL-native-isolation](goals.md#goal-native-isolation-contain-arbitrary-native-workloads), and [§GOAL-confidentiality](goals.md#goal-confidentiality-account-for-software-observable-leakage).
Each milestone must leave reusable contracts and evidence for the next one.

**Current stage: M0 foundation.** Runtime implementation begins at M1. All runtime
security claims remain planned in [§FS-assurance.status](functional-spec/FS-assurance.md#status-initial-claim-register). This document prepares
future work; it does not start or deploy development agents.

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

Expand [§FS-launch](functional-spec/FS-launch.md#fs-launch-establish-containment-before-executing-the-guest) into privilege reduction, descriptor handling, namespace/process
setup, enforcement installation, execution, signals, cancellation, and cleanup.
Cover partial setup and adversarial inheritance under [§FS-isolation.process](functional-spec/FS-isolation.md#process-memory-and-process-boundaries).

**Exit criteria:** establish the supported launch invariant across all specified
transitions and errors; connect abstract effects to OS bindings; document remaining
assumptions; test failures, leaked descriptors, privilege changes, and fork/exec.
Useful allowed execution must still be possible.

**Reusable output:** a launcher with compositional contracts, not a collection of
independent lemmas lacking an argument about the execution path.

## m3: Useful offline workspace sandbox

Deliver the first useful [§FS-compatibility.matrix](functional-spec/FS-compatibility.md#matrix-initial-compatibility-matrix) profile: read-only runtime,
private writable workspace, controlled I/O, confined descendants, native shell and
Python, and explicitly supported resource limits. Network/device access remains
denied unless introduced through a new supported contract.

**Exit criteria:** a usable library/CLI for that profile; object/handle/alias/race
reasoning for filesystem confinement; process and I/O confinement; defined limits
and teardown; adversarial regression tests; evidence report naming all remaining
kernel, compiler/runtime, and hardware assumptions.

**Reusable output:** a useful Linux workload profile and stable policy/backend
contracts. This is the earliest entry point for the optional M6 backend.

## m4: Linux and executable correspondence

Close the gap from Lean semantics to the actual executable and Linux enforcement
under [§AR-linux.correspondence](architecture/AR-linux.md#correspondence-reduce-the-linux-assumption) and [§AR-verification.artifacts](architecture/AR-verification.md#artifacts-bind-proofs-to-releases). Cover compilation,
native runtime, loader, foreign bindings, ABI, relevant Linux code and its transitive
dependencies, for a fixed kernel configuration.

**Exit criteria:** an explicit refinement chain for the advertised properties;
identified executable and kernel artifacts; all relevant obligations either
discharged or visible as remaining limitations that prevent the stronger claim.
Manual code maps and differential tests cannot substitute for a correspondence
proof. Avoid claiming the entire kernel has been verified.

**Reusable output:** semantics, proof connections, and reproducible artifact
evidence that can support more features and maintained Linux profiles.

## m5: Hardware-aware isolation

Fulfill [§FS-observations.hardware](functional-spec/FS-observations.md#hardware-software-observable-channels) for a named CPU/kernel/configuration profile.
Develop the observer model from M0 onward; investigate mechanisms such as resource
partitioning, scheduling controls, and restrictions only as justified by that model.

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

## next: Ready work for a future M1 assignment

Start with **M1.1**, then review its contracts before dependent implementation.
These are scoped work packages, not automatically launched agents.

| Work package | Depends on | Concrete output and review gate |
|---|---|---|
| M1.1 Source and contract slice | M0 | Source map for the pinned filter/exec path; selected ABI and filter subset; exact state/effect/failure contract; deviations and assumptions |
| M1.2 Decoder and bounds | M1.1 | Executable Lean decoder, machine-width proofs, malformed/boundary inputs, statement and axiom audit |
| M1.3 Launch transition proof | M1.1 | Success/failure model, install-before-exec theorem, nonvacuity witness, explicit OS premises |
| M1.4 Linux binding and demonstration | M1.2, M1.3 | Minimal binding, isolated integration profile, allowed/denied demo and injected setup failures |
| M1.5 Claim review and handoff | M1.4 | Full checks, declaration/artifact evidence record, reviewed remaining gaps, updated compatibility/status |

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
