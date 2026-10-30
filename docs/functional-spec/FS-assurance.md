# FS-assurance: Bind every advertised guarantee to auditable evidence

To meet [§GOAL-end-to-end.outcome](../goals.md#outcome-auditable-claims), distinguish target contracts, model theorems,
tests, assumptions, and deployed guarantees. Grund validates document structure
and citations; it cannot determine whether a security claim is true.

## evidence: Required claim record

For each security claim record: stable specification ID; plain-language scope;
exact Lean declarations and their types; transitive axioms and hypotheses;
implementation/source revision; executable hashes; compiler/runtime/FFI versions;
kernel version, configuration and image identity; hardware profile; observation
model; assumptions; open obligations; and reproducible proof/test commands.
An absent field must say why it is absent. A citation is not a proof binding.

The future machine-readable manifest must check that named declarations exist and
match the claimed artifacts. Until implemented, this register is a manual planning
record. Do not advertise automated artifact certification in M0.

## status: Initial claim register

| Claim | Contract | State | Present evidence | Missing connection |
|---|---|---|---|---|
| Validated authority | [§FS-policy](FS-policy.md#fs-policy-grant-only-explicit-supported-authority) | Planned | Specification | Implementation and theorem |
| Fail-closed launch | [§FS-launch](FS-launch.md#fs-launch-establish-containment-before-executing-the-guest), [§FS-filter-loading](FS-filter-loading.md#fs-filter-loading-prove-a-small-real-launch-boundary-first) | Planned | Specification and source map | Lean semantics, implementation, proof, OS binding |
| Native workload confinement | [§FS-isolation](FS-isolation.md#fs-isolation-confine-all-supported-guest-effects) | Planned | Specification | Launcher, filesystem/process model, enforcement proof |
| Bounded resources | [§FS-resources](FS-resources.md#fs-resources-define-and-enforce-supported-resource-limits) | Planned | Specification | Precise supported limits and enforcement |
| Functional confidentiality | [§FS-observations.logical](FS-observations.md#logical-functional-observations) | Planned | Observation requirements | Noninterference theorem and correspondence |
| Hardware-aware confidentiality | [§FS-observations.hardware](FS-observations.md#hardware-software-observable-channels) | Planned | Scope and research obligations | Model, mechanisms, proof, deployed profile |
| Deployed executable correctness | [§GOAL-end-to-end](../goals.md#goal-end-to-end-connect-the-policy-to-the-deployed-artifact) | Planned | Roadmap | Compiler/runtime/FFI and Linux correspondence |

No security theorems, certified executable artifacts, or supported production
profiles exist at M0. Tool/build checks demonstrate foundation consistency only.

## assumptions: Initial assumption and obligation register

These are prospective boundaries, not assertions that the current repository
already meets a security claim. Every later theorem must list the subset it uses.

| Key | Boundary | Early treatment | Planned disposition |
|---|---|---|---|
| A-logic | Lean logic, kernel/checker and faithful checking execution | Foundational trust, pinned checker | Audit axioms and proof-checking provenance; remain explicit |
| A-policy | Operator-selected policy, declared public/secret inputs and disclosures | Explicit environmental premise | Validate syntax/feasibility; cannot prove operator intent |
| A-model | Abstract effects represent all relevant concrete behavior | Open obligation | M1–M4 refinement, failure and interference coverage |
| A-linux | Relevant Linux enforcement, syscall semantics and transitive dependencies | Assumed in early Linux demonstrations | M4 connect contracts to pinned Linux implementation; expose remaining scope |
| A-executable | Lean compiler, native runtime, FFI, bindings and loader preserve semantics | Assumed for early binaries | M4 artifact correspondence; no perpetual hidden runtime gap |
| A-platform | Boot, configuration, privilege setup, deployment and updates match the profile | Explicit deployment assumptions | Bind artifact identities and configuration; verify relevant software setup |
| A-hardware | CPU/memory/device behavior matches the formal hardware model | Foundational fidelity assumption | M5 specify software-visible behavior; retain physical model fidelity openly |
| A-observer | Observation model covers the stated attacker | Open modeling obligation | Logical traces first, hardware-aware traces in M5; no silent exclusions |
| A-resources | Accounting/scheduling/termination implement each advertised bound | Assumed until established | Discharge per supported limit; otherwise narrow the claim |

## closure: Rules for stronger claims

Use states such as planned, model-proved, tested, and profile-verified with a stated
scope; multiple kinds of evidence can coexist. A model proof may still depend on
unproved assumptions. Reserve an end-to-end claim for a named profile whose
advertised chain is established, leaving only explicitly accepted foundational
assumptions. Do not reclassify unfinished Linux or compiler work as foundational
trust merely to close a milestone.

## updates: Evidence expires with its dependencies

Changes to specifications, theorem statements, code, toolchains, platform settings,
or artifacts must trigger review and revalidation of affected claims. An update
must not inherit an old certification merely because its version name is similar.
