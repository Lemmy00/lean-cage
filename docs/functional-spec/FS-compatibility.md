# FS-compatibility: Publish an explicit supported subset

To meet [§GOAL-reuse](../goals.md#goal-reuse-extend-milestones-without-discarding-their-foundations) and [§GOAL-native-isolation.outcome](../goals.md#outcome-useful-constrained-execution), expose a reusable library
and eventually a CLI for supported native Linux workloads. Bubblewrap is the
behavioral reference for selected features; compatibility is not presumed for all
its options or every Linux program.

## matrix: Initial compatibility matrix

M1 implements pure decoding and launch-order proofs for the fixed ABI/filter.
M2 adds conditional lifecycle proofs and a separate VM-only native helper.
M3 supplies the bounded offline workspace profile under [§FS-workspace](FS-workspace.md#fs-workspace-m3-offline-workspace-contract-version-1); acceptance
status and the model/native boundary are in [§FS-assurance.workspace](FS-assurance.md#workspace-m3-workspace-model-and-vm-evidence).

| Feature | First target | Current runtime support | Acceptance boundary |
|---|---|---|---|
| Filter input decoding | M1.2 | Pure decoder and model proofs; used by VM driver | [§FS-filter-loading.input.correctness](FS-filter-loading.md#inputcorrectness-decoder-proof-boundary) |
| Filter installation and install-before-exec | M1.3–M1.4 | Model-proved; 13-case native VM demonstration | [§FS-filter-loading.installation.model](FS-filter-loading.md#installationmodel-executable-launch-semantics-and-proof-obligations) and [§FS-assurance.demo](FS-assurance.md#demo-m14-isolated-linux-test-record); trusted single child, static x86-64 workload; Linux/native correspondence assumed |
| Privileges, descriptors, fork/exec, cleanup | M2 | Conditional model proofs; 43-case VM demonstration | [§FS-lifecycle.evidence](FS-lifecycle.md#evidence-acceptance-and-boundaries); root-helper static-native profile, trusted Linux/native effects; no workspace confinement |
| Read-only runtime and private workspace | M3 | Private copied workspace and frozen runtime in the designated VM | Object/handle/alias model; Linux VFS/descriptor effects remain conditional |
| Native shell and Python, offline I/O | M3 | Pinned Dash/Python, scripts/native code, bounded I/O and export | Named workflows, descendant model and VM cases in [§FS-workspace.profile](FS-workspace.md#profile-supported-environment-and-useful-workloads) |
| Network access, device access, broad option parity | Later extension | None | Denied until specified and verified |
| Resource budgets | M3 | cgroup memory/tasks/CPU bandwidth, sampled budgets/deadlines, workspace/output caps | [§FS-workspace.resources](FS-workspace.md#resources-units-ownership-and-failure); accounting/progress assumptions and measured overshoot |
| Hardware-aware confidentiality | M6 research | None | Exact supported hardware profile |
| seLe4n backend | Separate M6 track, entry permitted after M3 | Planned | Shared policy/result contracts, explicit workload/ABI subset, runnable execution and separate backend refinement/trust record |

## interface: Versioned commands

M3 implements `leancage check POLICY` for real policy/profile preflight,
`leancage run POLICY` for execution, and `leancage report RUN_ID` for the stored
result. [§FS-workspace.policy](FS-workspace.md#policy-bounded-typed-request) and [§FS-workspace.results](FS-workspace.md#results-entry-cancellation-and-bounded-transport) version the formats.
These commands support the designated disposable VM only. The experimental `leancage-m1` and `leancage-m2`
executables accept only their recorded VM test profiles; neither is a general
sandbox CLI or an authenticated external result API.
The caller-policy VM facade and root build are specified in [§FS-linux-product.operation](FS-linux-product.md#operation-run-a-callers-workload-through-one-supported-interface).
Keep the core policy independent of CLI syntax; broaden this interface only with
a versioned contract and renewed evidence.

## reference: Compare without overstating equivalence

Pin the reference implementation and the supported behaviors. Record intentional
departures, especially stricter validation. Differential tests show tested
agreement only. Claim formal correspondence with reference code only when a
separate semantics-and-refinement proof actually establishes it.
