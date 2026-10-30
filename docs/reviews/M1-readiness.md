# M1 readiness review and M2/M3 planning

Reviewed on 2026-10-30 against M1 commit
[`fad5c7308fdcc2c2f64f3ba9dfa99c41a8d9eba5`](https://github.com/Lemmy00/lean-cage/commit/fad5c7308fdcc2c2f64f3ba9dfa99c41a8d9eba5).
The review covers the implementation, theorem statements, audit tooling, native
call boundary, test configuration, and evidence for [§RM-roadmap.m1](../roadmap.md#m1-first-executable-proof-slice).

**Verdict: accept M1 for its stated filter-decoding and launch-order scope.**
No blocking discrepancy was found within that scope. The distinction between
model proofs, a tested native driver, and unproved native/Linux correspondence
is explicit in [§FS-assurance](../functional-spec/FS-assurance.md#fs-assurance-bind-every-advertised-guarantee-to-auditable-evidence). M2 remains unimplemented. The endpoint is unchanged;
the next milestones need finer contracts and work packages, not a replacement
of the M1 approach.

## What was checked

| M1 acceptance criterion | Reviewed evidence | Boundary |
|---|---|---|
| Exact byte decoding and deterministic rejection | `decode_ok_iff`, word reconstruction, bounds and first-mismatch proofs; `ValidInput` is expressed through independent byte equations | One fixed native x86-64 ABI and canonical nine-instruction filter |
| Launch ordering and terminal failure | Exact successful histories, receipt preservation, failure/termination absorption, and replay/reachability equivalence | Finite abstract traces under truthful OS observations |
| Actual validation and nonvacuity | Decoder-linked verdict/invalid-input theorems and concrete success/failure witnesses | Entry acceptance is still a Boolean supplied from the trusted profile |
| Proof integrity | Fresh `./scripts/check.sh`: 43 authored claims within 445 inventoried theorem declarations; exact types/axiom sets and 39 source/dependency/evidence hashes match | Allowed transitive axioms are only `propext`, `Classical.choice`, and `Quot.sound`; counts are inventory, not security strength |
| Negative and boundary tests | 21 Python tests and 58 Lean guards pass, including deliberately forbidden axioms, malformed inputs, and erroneous trace/evidence cases | Tests supplement the universal decoder/trace theorems |
| Concrete native setup | Layout assertions, bounded field copying, NNP/install/direct-exec order, terminal child errors, and explicitly separate parent supervision | The C driver is manually mapped to the model; it is not proved equivalent |
| Isolated Linux demonstration | Independent replay passes all 13 cases with the same source map, guest-file hashes, and recorded artifact hashes as the archived run | Functional demonstration, not confinement or hardware confidentiality |

The native driver build passed. Before the independent replay, all **62 recorded
artifact hashes** were checked against the available local artifacts. This review
reused that matching kernel image; it did not rebuild Linux from source. The
original M1 evidence separately records its fresh source/kernel build.

The original milestone evidence remains unchanged. The independent replay is
retained in [structured evidence](../../assurance/reviews/m1-readiness-vm.json)
and its [raw serial transcript](../../assurance/reviews/m1-readiness-vm.log).
It records the same 13-case outcomes, not an expanded workload or threat model.

Reviewed identities:

| Record | SHA-256 |
|---|---|
| `assurance/filter-decoder.json` | `877584a38b1d6db3860f3abc99f62e80711954e1c3e4a929ac33de1c2a774dea` |
| Original `assurance/m1-vm-evidence.json` | `4d918dfb9f0af095c5dd55de5db5d1b6d04112b847ecc45cb94396104af1669d` |
| Independent `assurance/reviews/m1-readiness-vm.json` | `d04aaf4235e40d3144131ba1317dcc54082fe29cc6df6b4d4bd515d2fba6d33f` |

A packaging fix preserves raw serial logs with `.gitattributes`: Git must retain
their CRLF bytes because the evidence hashes those exact bytes. The staged original
transcript was checked against its recorded SHA-256 before the M1 commit.

## Findings that change the next plan

These are limitations already compatible with M1's scope. They are gates for the
stronger claims planned in M2/M3, not evidence of an M1 isolation guarantee.

| Finding | Concrete basis | Required follow-through |
|---|---|---|
| The test profile cannot exercise the next mechanisms | `tests/vm/linux-6.18.59.config` disables `CONFIG_NAMESPACES`, `CONFIG_CGROUPS`, `CONFIG_UNIX`, `CONFIG_INET`, and `CONFIG_BINFMT_SCRIPT`; security-framework support is also disabled | M2.2 adds a separate capable profile with positive controls. Choose needed features explicitly; leave the M1 profile/evidence reproducible |
| Trusted entry conditions do substantial work | [§FS-filter-loading.installation.entry](../functional-spec/FS-filter-loading.md#installationentry-entry-conditions-and-interference) excludes hostile inherited handlers/tracers/shared writers; the VM init drops groups/UID/GID before invoking the launcher | M2.1 inventories those premises; M2.3–M2.5 establish or explicitly validate/reject them, with a precise residual host trust boundary |
| The theorem and native driver are distinct programs | `Launch/Model.lean` checks abstract events; `native/leancage_m1.c` performs child setup; `nativeLaunch` is an external override | Choose the executable controller/native boundary in M2.1; compose its effects in M2.6 and keep native refinement on the M4 ledger |
| Supervision needs its own contract | Parent read/wait/protocol results are outside the child model; guest exit 125 is ambiguous in the fixture; no cancellation API or descendant supervisor exists | M2.5 defines process ownership and typed outcomes, including unknown guest-entry status, cancellation races and teardown failures |
| Decoder correctness does not prove the policy action | The filter semantics is currently a private reference interpreter with 14 examples; the canonical filter allows almost every native syscall | M2.6 proves the selected bytecode action generally; M3.3 separately proves any policy-to-filter extension and preserves/version-controls the old decoder contract |
| Static trusted images do not establish a reusable workspace | ELF preflight closes the checked descriptor before path-based exec; file stability is assumed; only the static fixture is supported | M2 fixes the chosen handle/identity contract; M3 adds the actual shell/Python loader/runtime closure, filesystem authority, races, and cross-process policy |
| Archived evidence is not a certificate for a new build | `--check-evidence` checks source/transcript consistency and cases, while recording rather than certifying native artifacts | M2.7/M3.6 require complete profile/evidence schema checks and distinguish historical evidence, current artifact identity, and fresh replay; preserve the M4 correspondence obligation |

The kernel's [seccomp documentation](https://docs.kernel.org/6.18/userspace-api/seccomp_filter.html)
describes syscall filtering as one isolation mechanism, rather than a complete
sandbox. Its [no-new-privileges contract](https://docs.kernel.org/6.18/userspace-api/no_new_privs.html)
does not drop existing authority or prohibit all non-exec privilege changes.
Those distinctions motivate M2's credential/handle work. The
[cgroup v2 interface](https://docs.kernel.org/6.18/admin-guide/cgroup-v2.html)
provides resource-controller semantics that M3 must select and model explicitly;
a test harness timeout is not their replacement. These documents guide the
contracts and do not prove the kernel implementation.

## Updated sequence

The canonical work packages and acceptance gates are in [§RM-roadmap.m2](../roadmap.md#m2-verified-launcher-lifecycle) and
[§RM-roadmap.m3](../roadmap.md#m3-useful-offline-workspace-sandbox). Start with **M2.1: lifecycle contract and execution design**:

1. Classify every M1 entry premise as establish, validate, reject, or retain with
   an explicit environmental justification.
2. Specify owned state, process/descriptor identity, public observations, success,
   failure, cancellation, and cleanup outcomes under [§FS-launch](../functional-spec/FS-launch.md#fs-launch-establish-containment-before-executing-the-guest).
3. Select one privilege/helper/runtime architecture and a capable isolated test
   profile. Map concrete operations to the model before enlarging the native code.
4. Define M2's proof/test gates and the first native correspondence obligation
   for M4. Preserve the old decoder/launch contracts or explicitly version a
   reviewed refinement.

M3 then supplies actual workspace authority, pinned shell/Python execution,
offline/process boundaries, resource budgets, and a usable evidence-reporting API.
Negative tests need positive controls: a missing network stack or resource
controller must not masquerade as successful confinement.

Begin M4's semantics/FFI inventory during M2, rather than postponing every concrete
connection until a large runtime exists. Keep public/secret observation decisions
visible during M2/M3 for [§FS-observations](../functional-spec/FS-observations.md#fs-observations-state-exactly-what-an-attacker-may-observe); the hardware-channel proof remains M5.
The optional seLe4n entry gate stays after M3. No M2 implementation, production
release, or agent deployment is part of this review.
