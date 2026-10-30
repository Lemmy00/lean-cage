# FS-compatibility: Publish an explicit supported subset

To meet [§GOAL-reuse](../goals.md#goal-reuse-extend-milestones-without-discarding-their-foundations) and [§GOAL-native-isolation.outcome](../goals.md#outcome-useful-constrained-execution), expose a reusable library
and eventually a CLI for supported native Linux workloads. Bubblewrap is the
behavioral reference for selected features; compatibility is not presumed for all
its options or every Linux program.

## matrix: Initial compatibility matrix

All rows are planned; M0 supplies documentation and tooling only.

| Feature | First target | Current runtime support | Acceptance boundary |
|---|---|---|---|
| Filter input and install-before-exec | M1 | None | One explicit ABI and supported filter form |
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
commands do not exist in M0. Version policy and report formats when the first
implementation needs them; keep core policy independent of CLI syntax.

## reference: Compare without overstating equivalence

Pin the reference implementation and the supported behaviors. Record intentional
departures, especially stricter validation. Differential tests show tested
agreement only. Claim formal correspondence with reference code only when a
separate semantics-and-refinement proof actually establishes it.
