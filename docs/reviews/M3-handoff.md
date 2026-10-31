# M3 workspace implementation and handoff review

This review covers [§RM-roadmap.m3](../roadmap.md#m3-useful-offline-workspace-sandbox) and [§FS-workspace](../functional-spec/FS-workspace.md#fs-workspace-m3-offline-workspace-contract-version-1) for
`linux-x86_64-offline-workspace-m3-v1`. It distinguishes conditional model proofs,
native implementation, passive artifact inspection and disposable-VM evidence.
It is not an independent security review or production certification.

**Verdict: M3.1–M3.7 accepted for the stated conditional offline workspace
profile.** The full repository gate and fresh source-bound VM replay passed on
2026-10-31. Native/Linux/executable correspondence and hardware confidentiality
remain open M4/M5 obligations.

## Work packages

| Package | Delivered output | Evidence location |
|---|---|---|
| M3.1 | Versioned authority, workload, policy, disclosure, limit and transport contracts; pinned runtime and consequential decisions | [§FS-workspace](../functional-spec/FS-workspace.md#fs-workspace-m3-offline-workspace-contract-version-1), [§AR-workspace](../architecture/AR-workspace.md#ar-workspace-m3-authority-model-linux-realization-and-evidence-plan), [§DA-m3-profile](../decisions/architectural/DA-m3-profile.md#da-m3-profile-frozen-runtime-copied-workspace-and-distinct-run-authority), `profiles/m3/` |
| M3.2 | Immutable runtime, copied input tree/stdin, private writable workspace, explicit object/handle aliases, post-extinction export | `Authority.lean`, `AuthorityProofs.lean`, `native/m3_artifacts.h`, filesystem/alias/import/export cases |
| M3.3 | Dynamic shell/Python/native workspace execution, bounded policy parser, separate syscall filter, private entry/final frames | `Policy.lean`, `Filter.lean`, `Lifecycle.lean`, `Results.lean`; complete native filter byte comparison |
| M3.4 | Separate run UID/GID and namespaces, denied network/IPC/tracing/descriptor transfer, overlapping sibling workloads | `ProcessProofs.lean`; in-VM IPv4/IPv6/Unix, SysV/POSIX shared-memory and tracing controls |
| M3.5 | Read-back cgroup limits, sampled CPU/wall cancellation, task/OOM counters, workspace/output caps, admission reservation and quarantine | `Resources.lean`; real limit cases, six cancellation/death boundaries and surviving sentinel |
| M3.6 | Actual check/run/report commands and library; typed private result, stored stream/export artifacts and identity record | `API.lean`, `Main.lean`; three VM API checks using the same helper |
| M3.7 | Composed model results, full statement/axiom inventory, strict source/artifact/transcript gate, moved-checkout and tamper tests | `Proofs.lean`, `scripts/audit_m3.py`, `scripts/run_m3_vm.py`, `assurance/m3-*` |

## Reviewed propositions and their limits

The 60 named claims and all 419 generated/project theorem declarations across
12 modules are recorded
with full types and transitive axioms in `assurance/m3-claims.json`. The actual
checked environment is queried, including Main; ordinary checks do not regenerate
expectations. Only `propext`, `Classical.choice` and `Quot.sound` occur in the audited
union. No security claim uses unfinished, custom or compiler-trust axioms.

| Original obligation | Actual declarations and quantified claim |
|---|---|
| `validate_iff` | `validatePolicy_iff` proves exact typed limits/argv acceptance. `decodePolicy_iff` decomposes acceptance for every byte array into structural parsing plus those checks; `decodePolicy_bounds` and `accepted_policy_filter_action` link an actual accepted request to bounds and the universal filter action. This is not an independent RFC JSON grammar theorem or parser/compiler refinement. |
| `reachable_authority` | `reachable_issued_handles` starts from closed inherited handles and arbitrary objects/names, and covers every finite request list. Handles retain live generations and read/write rights across alias/rename/dup/allocation and ordinary external writes. `reachable_unguarded_read` and `issued_write_preserves_protected` apply to held-handle operations without fresh ownership checks. |
| `guest_preserves_protected` | Every guest-origin operation preserves any existing nonwritable object; `guest_trace_preserves_protected` extends to all guest-only traces. `runtime_trace_preserved` additionally includes allowed ordinary external writes. Outside/sibling writes by their own owners are allowed and are not falsely claimed invariant. |
| `descendant_inherits` | Fork copies actual full credentials, scope, root, namespace, grants, NNP and filter. `reachable_processes_safe` establishes and preserves the invariant from an empty process table through admission/fork/exec/exit/denied-migration events. |
| `policy_filter_action` | Every UInt32 architecture/syscall/low-argument/high-argument tuple executes the generated cBPF instruction list to its reviewed action. `program_action` also quantifies over arbitrary syscall tables. The native header is compared byte-for-byte with Lean emission; Linux BPF/ABI correspondence remains open. |
| `entry_requires_receipts` | First entry needs every receipt and no prior failure; every entered state reachable from the empty lifecycle has the exact ordered receipt list. Failure, cancellation, lost reports and guest output remain transitions. |
| `private_report_knowledge` | Arbitrary lists of guest byte observations leave supervisor knowledge unchanged. `decodeResult_valid` establishes every accepted public frame's concrete bounds/status checks. These do not prove native pipe ownership or C framing; those are explicit local contracts and tested mappings. |
| `cancel_not_completion` | Cancellation preserves possible live scope and does not release it. `release_requires_extinction`, `reuse_requires_extinction` and counter-loss lemmas prevent a request, lost report or missing sample becoming successful completion. |
| `resource_scope` | Every member of the established process invariant has this run's scope. Monotone delivered samples trigger CPU/deadline cancellation; OOM evidence requires counter increase. Task, capture and reservation bounds are separate pure results. No theorem supplies Linux accounting correctness or unconditional response-time/overshoot limits. |
| `lifecycle_projection` | Successful M3 receipt order erases to the preserved M2 operation plan. It does not inherit M2's fixed UID, static ELF or nine-instruction decoder invariant. |

`reachable_model_safety` composes runtime preservation, entry prerequisites,
authorized reads, issued-handle preservation and reachable process inheritance.
It quantifies over the component traces; a native concurrent execution satisfying
all local operation contracts still requires the M4 simulation. `useful_read_write`,
`useful_launch_trace`, `useful_descendants` and `useful_execution` provide inhabited
success witnesses, checked by Lean's kernel. The filter proofs are universal,
not exhaustive tests over a sampled set.

The object map models names separately from open descriptions and allocation
generations. It is an authority/effect interface, not a complete Linux path,
mount, mmap or inode implementation. Network/IPC and process-access effects rely
on the filter action plus explicit namespace/credential contracts. M4 must connect
all concrete syscall paths, including aliases and pointer arguments, to those
interfaces. No functional noninterference theorem is claimed; authorized output
can disclose the guest's input, and hardware observations remain M5.

## Native source and effect map

| Portable boundary | Native path | Unproved concrete effect |
|---|---|---|
| Bounded policy and plan | `Main.main`, `API.planArgs`/`invoke`, helper `main` validation | UTF-8/JSON/argv serialization, Lean runtime and C integer/buffer correspondence |
| Frozen identity and input | `m3_runtime.py`, `m3_elf.py`, `import_tree`, `snapshot_stdin`, SHA-256 helper | OCI composition, cryptographic identity, copied objects, sealed memfd and immutable operator store |
| Object roots and handles | `prepare_resources`, `construct_root`, `guest` | Private propagation, mounts/chroot, close_range, VFS/descriptor/mapping effects and capability checks |
| Credentials and descendants | `credentials`, `namespace_init`, allocator | All ID/capability forms, reserved UID lifetime, fork/thread/exec inheritance, PID namespaces and ptrace entry observation |
| Filter | `Filter.bytes`, generated `m3_filter.h`, NNP/seccomp calls | Exact loaded ABI bytes, Linux interpreter/JIT and syscall semantics |
| Resource scope and cleanup | cgroup helpers, collector, `cleanup` | Readback/placement, charged memory/task counts/CPU accounting, kill/reap/extinction, scheduling and release |
| Private report/output/export | `send_frame`/`decode_frame`, `capture`, `export_workspace`, `Results.decodeResult` | Pipe ownership, native concurrency, partial I/O and artifact stability after extinction |

Unknown accounting yields null usage/peak/event/time/overshoot values; output
storage failures yield unknown capture quantities. A real leader exit racing a
cancellation retains both observations. Helper/controller death does not invent
an authenticated final frame or cleanup receipt. Its UID and admission capacity
remain quarantined until a trusted recovery path establishes extinction/release;
a reusable host service or automated recovery daemon is not supplied by this VM
profile.

## Runtime, kernel and artifact identity

The pinned Python 3.13.18/Dash 0.5.12-2/glibc 2.36 runtime manifest is
`sha256:70bda1e795ded2a684ef9815955e05829b14ee5bb5c3eb2a940648e88f10fce9`.
Four compressed layers and diff IDs, all 6572 merged non-root entries, critical
entrypoint/loader hashes and 97 package notice hashes are inspected passively.
The 792-object ELF inventory reports no missing required dependency; `_tkinter`'s
missing Tcl/Tk libraries match the explicitly unsupported GUI subset. Presence
and hashes do not prove dynamic search, symbol binding, runtime safety or an
upstream reproducible build. Runtime binaries and notices remain cached locally,
not relicensed or vendored as project source.

Linux 6.18.59 uses commit `1253a6aa5d104312bf0992afacc15220ae35bdf9` and archive
SHA-256 `53a55ac9863a5547e292b8e381d4e4c2240dd1127d5428a7c44dbc550be23963`.
The separate M3 configuration adds file locking and shebang execution to M2;
newly visible NFS/SMB server options stay disabled. `CONFIG_BLOCK=n` leaves swap
unavailable, checked without a hidden fallback. QEMU 8.2.2 TCG runs one `max` vCPU,
2048 MiB, ACPI-PM clocksource, no NIC, disk, host mount or KVM. This identifies a
functional virtual CPU profile, not physical CPU/microcode or timing assurance.

`assurance/m3-vm-evidence.json` records exact source hashes, compiler/libc/Lean/QEMU
versions, kernel/configuration/helper/controller/filter/image/firmware and library
hashes, normalized VM command, explicit emulator library/module environment
overrides and timeout. Other host environment values are inherited and are not
a reproducible-environment attestation. `assurance/m3-image-inventory.json`
records every image entry. The transcript contains trusted hex-encoded guest
captures and typed outcomes; guest output cannot become a harness control line.
The VM's `/m3-assurance.json` binds source/helper/controller identities and residual
assumptions. Per-run `identity.json` hashes the normalized policy plan and filter.
Hashes identify artifacts; they do not prove source-to-executable correctness.

## Validation and preservation

The fresh source-bound replay passes **60 workload cases, three API checks and
six cancellation/death boundaries**. It records 67 source identities, 70 compiled/
runtime/emulator artifacts and 6611 image entries. The supported Linux kernel was
built from the pinned archive using the reviewed separate configuration. All
positive controls and unrelated sentinel checks pass.

Observed examples from that replay are evidence, not unconditional bounds:

| Case | Actual observation |
|---|---|
| CPU budget | 30000 us requested; 33768 us final usage; 3768 us observed overshoot; cancellation and cleanup complete |
| Wall deadline | 200 ms requested; 212 ms elapsed; 12 ms observed overshoot; stopped/sleeping cases covered |
| Memory | 32 MiB limit; 33554432-byte recorded peak; SIGKILL with two cgroup OOM-kill events |
| Task/thread caps | Each four-task case records one pids-limit event; the useful parent completes and descendants are removed |
| Admission | Oversubscribed memory/workspace/export reservation rejects with EAGAIN before an identity or guest is admitted |

The [acceptance matrix](M3-acceptance.md) maps every contract group to actual tests
and model obligations, without claiming every Linux interleaving was tested.
The handoff passed `./scripts/grund.sh fmt --write`, `./scripts/check.sh`, fresh
`python3 scripts/run_m3_vm.py` and `--check-artifacts`. The full gate includes
71 Python tests (21 M1, 21 M2, 29 M3), 168 Lean guards (58 M1, 33 M2, 77 M3),
all three declaration/type/axiom audits, strict native compilation and archived
VM validation. The M3 audit binds 82 source/dependency/evidence identities and
checks 419 theorem declarations, including all 60 named claims. Its exact emitted
filter SHA-256 is `c9c50808737ec7ba2f285a7aef7baa86de3aad984a3106f54d89b0002120e93e`.
Historical evidence checking works from a moved checkout without `.tools/m3vm`;
it rejects stale/mixed sources, altered profiles/artifacts, missing/duplicate/
reordered observations, missing controls/API/death cases and timeouts.

All 445 M1 and 274 M2 theorem statements/axioms remain preserved. Their native
sources, dependencies, toolchains, kernel configurations and raw VM evidence are
unchanged. Shared assurance documentation and the extended check script require
reviewed source-fingerprint updates in the current manifests; the independent M1
baseline manifest remains byte-for-byte unchanged. No branch was published and no
host service, shared kernel or active workload was changed.

## Residual obligations and next assignment

The original eight M2 M4 obligations and all eight additions in
[§AR-workspace.correspondence](../architecture/AR-workspace.md#correspondence-additional-open-m4-boundaries) remain open: policy/parser serialization, filesystem,
loader, identities/processes, filter, resources, results and artifact connection.
Root-owned input/runtime/allocator integrity, reserved identities, truthful local
Linux effects, compiler/runtime/FFI/crypto correctness, emulator/firmware and
hardware fidelity remain explicit. Liveness needs scheduled supervision, signal
progress and terminating kernel operations; no finite sampling-overshoot bound
is promised without those premises. Retained result storage remains operator
provisioning, beyond the active admission ledger.

The next work is the bounded CompCert Clight feasibility experiment in
[§AR-workspace.experiment](../architecture/AR-workspace.md#experiment-bounded-first-native-semantics-connection), using the actual dispatcher/error/framing slice and
identified semantics/tool pins. It is not run or proved by M3. A Rocq result would
still need an explicit Lean connection, and it would not certify the existing GCC
binary or Linux external effects. Preserve the hardware-channel destination in
[§FS-observations.hardware](../functional-spec/FS-observations.md#hardware-software-observable-channels) throughout that work.
