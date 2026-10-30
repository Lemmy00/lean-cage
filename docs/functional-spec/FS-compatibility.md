# FS-compatibility: Publish an explicit supported subset

To meet [§GOAL-reuse](../goals.md#goal-reuse-extend-milestones-without-discarding-their-foundations) and [§GOAL-native-isolation.outcome](../goals.md#outcome-useful-constrained-execution), expose a reusable library
and eventually a CLI for supported native Linux workloads. Bubblewrap is the
behavioral reference for selected features; compatibility is not presumed for all
its options or every Linux program.

## matrix: Initial compatibility matrix

M1 implements pure decoding and launch-order proofs for the fixed ABI/filter,
plus a VM-only native demonstration. Broader sandbox runtime rows remain planned.

| Feature | First target | Current runtime support | Acceptance boundary |
|---|---|---|---|
| Filter input decoding | M1.2 | Pure decoder and model proofs; used by VM driver | [§FS-filter-loading.input.correctness](FS-filter-loading.md#inputcorrectness-decoder-proof-boundary) |
| Filter installation and install-before-exec | M1.3–M1.4 | Model-proved; 13-case native VM demonstration | [§FS-filter-loading.installation.model](FS-filter-loading.md#installationmodel-executable-launch-semantics-and-proof-obligations) and [§FS-assurance.demo](FS-assurance.md#demo-m14-isolated-linux-test-record); trusted single child, static x86-64 workload; Linux/native correspondence assumed |
| Privileges, descriptors, fork/exec, cleanup | M2 | None | Published launch-state and OS contracts |
| Read-only runtime and private workspace | M3 | None | Object/handle/race-aware confinement |
| Native shell and Python, offline I/O | M3 | None | Named workloads, controlled streams, confined descendants |
| Network access, device access, broad option parity | Later extension | None | Denied until specified and verified |
| Resource budgets | M3 onward | None | Only documented bounds with enforcement evidence |
| Hardware-aware confidentiality | M5 | None | Exact supported hardware profile |
| seLe4n backend | M6 | None | Separate backend and assumptions |

## interface: Future commands

The planned interfaces are `leancage check` for policy/profile preflight,
`leancage run` for execution, and `leancage report` for assurance evidence. These
commands do not exist at M1. The experimental `leancage-m1` executable accepts
only the recorded VM test profile and is not a general sandbox CLI.
Version policy and report formats when the first
implementation needs them; keep core policy independent of CLI syntax.

## reference: Compare without overstating equivalence

Pin the reference implementation and the supported behaviors. Record intentional
departures, especially stricter validation. Differential tests show tested
agreement only. Claim formal correspondence with reference code only when a
separate semantics-and-refinement proof actually establishes it.
