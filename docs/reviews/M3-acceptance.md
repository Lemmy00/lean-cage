# M3 acceptance matrix

This maps [§FS-workspace](../functional-spec/FS-workspace.md#fs-workspace-m3-offline-workspace-contract-version-1) and [§AR-workspace.acceptance](../architecture/AR-workspace.md#acceptance-coverage-and-handoff-gate) to the implemented regression
suite. The accepted artifact record and final verdict are in [the handoff](M3-handoff.md).
All guest programs, hostile attempts, peer controls and process-death experiments
run only in the designated disposable VM. The original obligation names below
remain design targets; exact declarations and limits are reviewed in the handoff.

| Case group | Allowed/control execution | Denied, failure or race execution | Proof obligation / owner |
|---|---|---|---|
| policy | Frozen example; exact bounds | Unknown/duplicate fields, noninteger/overflow, invalid UTF-8/NUL, long argv, unsupported profile or digest | `validate_iff`; M3.3 |
| snapshot | Frozen directories/regular files; repeated blobs copied independently | Bad hash/size, duplicate paths, dot-dot, links/special files; source changes after snapshot | `reachable_authority`; M3.2 |
| runtime | Exact shell/Python, loader and data reads | Runtime write/chmod/unlink/mmap, stale digest, replaced loader/config, missing dependency | `entry_requires_receipts`, `guest_preserves_protected`; M3.2–3 |
| workspace | Read/write/create/remove, executable script/native file | Traversal to host/sibling; concurrent external source rename/write; outside inherited aliases | `reachable_authority`; M3.2 |
| aliases | Internal symlink/hard-link, held fd after unlink | Cross-root links, dirfd/cwd/proc magic link, rename-vs-open, runtime write alias | `guest_preserves_protected`; M3.2 |
| mounts | Correct private root and workspace | Failed pivot/mount/remount, shared propagation, old-root handle, mount/setns/unshare attempt | `entry_requires_receipts`; M3.2–3 |
| proc_devices | Own PID view, null/zero/urandom, own fd links | Host/global proc, init memory/fds, raw devices, device mknod, sysfs/cgroupfs | `reachable_authority`; M3.2–4 |
| shell | Pipeline, redirection, cwd/env, exit 125, child status | Pipeline child failure, SIGPIPE/output cap; guest prints forged result | `descendant_inherits`, `private_report_knowledge`; M3.3 |
| python | JSON/hash/files/imports; subprocess; thread join | Missing required module/loader, arbitrary workspace extension; unsupported GUI/network | `descendant_inherits`; M3.3 |
| filter | Every allowed syscall family and libc fallback | Wrong ABI/x32, unlisted syscall, clone flags, malformed program, failed NNP/install | `policy_filter_action`; M3.3 |
| process | Same-run fork/exec/signals and threads | Foreign ptrace/process_vm/pidfd_getfd/signals, PID reuse, double fork/setsid | `descendant_inherits`, `reachable_authority`; M3.3–4 |
| siblings | Two concurrent distinct run IDs/UIDs with useful writes | Read/write/trace/signal sibling; UID exhaustion/reuse while cleanup unknown | `guest_preserves_protected`; M3.4 |
| network | In-VM IPv4/IPv6/Unix peers work outside restricted scope | Guest socket/connect/socketpair/raw/packet and fd transfer; no external network dependency | `reachable_authority`; M3.4 |
| ipc | In-VM SysV/POSIX shared-memory peers work as controls | Guest SysV/foreign shared objects, inherited socket/queue/IPC handles | `reachable_authority`; M3.4 |
| memory | Allocation below configured charge limit | Actual cgroup OOM, swap/control failure, missing mechanism; distinguish SIGKILL without OOM counter | `resource_scope`; M3.5 |
| tasks | Multiple processes and threads below cap | Fork/thread creation limit; no migration escape; unrelated sentinel continues | `resource_scope`; M3.5 |
| cpu | CPU accounting and bandwidth control progress | Aggregate descendants consume budget; recorded sampling overshoot; counter failure | `resource_scope`; M3.5 |
| deadline | Timely normal exit | Busy/sleeping/stopped guest, delayed supervisor, setup watchdog | `cancel_not_completion`; M3.5 |
| workspace_limits | Writes/import/export below byte/inode caps | ENOSPC, inode exhaustion, oversize import/export, retained fd on deleted file | `resource_scope`; M3.2/5 |
| streams | Exact stdin and independent stdout/stderr prefixes | Zero/boundary cap, slow/closed reader, simultaneous floods, partial writes/storage failure | `private_report_knowledge`; M3.3/6 |
| reports | Genuine framed entry/final result | Every truncated prefix, forged guest output, wrong run/seq/kind/length, duplicate final, dropped channel | `private_report_knowledge`; M3.3/6 |
| cancellation | Owned death followed by release/export | Before entry, exec race, natural exit race, descendant survives leader, repeat cancellation | `cancel_not_completion`; M3.5 |
| supervisor_death | Sentinel survives ordinary run | Controller/helper/init death including pre-arming windows; no false cleanup/reuse | `entry_requires_receipts`, `cancel_not_completion`; M3.5 |
| export | Frozen post-extinction files and encoded raw names | Symlink/device/socket/FIFO never followed; hard-link flatten; read/storage error | `guest_preserves_protected`, `private_report_knowledge`; M3.6 |
| failures | Successful complete setup | Failure at every root/handle/credential/cgroup/NNP/filter/exec/report boundary | `entry_requires_receipts`; M3.2–6 |
| evidence | Full statement/axiom/source/artifact gate; moved checkout | Stale/mixed identities, missing/reordered cases, missing control/sentinel, timeout/harness failure | [§FS-assurance.evidence](../functional-spec/FS-assurance.md#evidence-required-claim-record); M3.7 |

## Concrete coverage

| Contract groups | Implemented evidence |
|---|---|
| policy | Real Lean decoder tested by `test_policy.py`; exact typed bounds/decode decomposition proofs; malformed/duplicate keys, bad UTF-8/NUL, unknown schema/profile/digest, overflow and argument/resource boundaries |
| snapshot | `snapshot_stdin_export`, `snapshot_bad_hash`, `snapshot_duplicate`, `snapshot_traversal`, `snapshot_link_record`, `stdin_oversize`; repeated input blobs become independent copied files. External source paths are absent from the launch interface. |
| runtime / mounts | Passive layer/hash/license/ELF closure checks; tampered graph, traversal/alias/whiteout/link tests; `filesystem_denials`, `runtime_aliases`, `fault_mount_fail`, `fault_namespace_fail`; immutable runtime dependency identity is checked while building the image. |
| workspace / aliases | `aliases`, `rename_open_race`, `workspace_exec`, `workspace_native_exec`, `inherited_handles`; arbitrary model aliases and external object writes, including unguarded held-handle authority theorems |
| proc / devices | `proc_devices`, `filesystem_denials`, `runtime_aliases`; private proc/root/fd visibility, working null/zero/urandom; privileged device creation remains a Linux capability/nodev obligation |
| shell / Python | `shell`, `python`, `snapshot_stdin_export`, script/native execution; pipeline/status, JSON/UTF-8/hash/files, module import, subprocess and joined threads; GUI/Tk deliberately unsupported |
| filter / process | Universal action theorem and full emitted-byte comparison; `clone_flags`, `x32`, `i386`, `network_ipc_process_denials`, `signal`, `exit125`, `descendant_cleanup`; inherited credential/root/filter/scope trace proof |
| siblings / network / IPC | Concurrent useful `concurrent_a`/`concurrent_b` with measured overlap and distinct UIDs; inaccessible sibling roots, denied external calls and init signal; working trusted IPv4/IPv6/Unix/SysV/POSIX/tracing controls in init |
| memory / tasks / CPU | `oom` with actual OOM counter, `task_limit` and `thread_limit` with task-denial counters, `cpu_budget`, `fault_accounting`; native readback and model scope/sampling statements |
| deadline / workspace / admission | `deadline`, `stopped_guest`, `workspace_bytes`, `workspace_inodes`, `reservation_rejected`; reservation, task/capture bounds and run-ID exhaustion/reuse lemmas |
| streams / reports | `stdout_cap`, `stderr_cap`, `both_streams`, `output_boundary`, `forged_report`, `fault_output_storage`, `fault_output_close`; every truncated public-frame prefix and malformed tags/widths/reserved fields; short/dropped/duplicate/wrong-sequence internal reports and error pipe failures |
| cancellation / death | `exit_cancel_race`, orphan cleanup, plus `cancel_after_entry`, `helper_death`, `controller_death`, `init_death`, `helper_before_fork`, `controller_before_arm`; extinction, quarantine and live sentinel checked with pidfds |
| export | `snapshot_stdin_export` checks raw filename encoding, omitted symlink/FIFO and flattened hard links; `export_hardlink_bound` returns explicit failed export while retaining the real guest exit |
| setup / API | Namespace/mount/handle/credential/cgroup/NNP/filter/exec injected failures; successful `preflight` enters no guest; actual check/run/report validates snapshots, captures, export and the same persisted result |
| evidence | `test_audit.py` and `test_evidence.py`: full types/axioms, source/profile/artifact/schema/counter/control/sentinel tampering, missing/duplicate/reordered/timeout records, concurrent overlap, omitted API/death checks and a moved checkout without the original cache |

Fault names explicitly label test injection. Positive controls prove that the
selected mechanisms work in a trusted VM peer; an infrastructure timeout or
missing mechanism fails the suite and is never counted as a denied attack.
Every ordinary case checks the private result, expected output/artifact state,
owned-scope extinction and unrelated sentinel survival.

The suite is a finite regression set, not a claim to test every allowed syscall,
VFS/mmap/interference path, PID reuse, allocator exhaustion sequence, scheduler
delay, kernel error or repeated cancellation. General model quantification and
filter action cover their stated interfaces; the native mapping for unenumerated
interleavings remains in [§AR-workspace.correspondence](../architecture/AR-workspace.md#correspondence-additional-open-m4-boundaries). In particular, ELF dependency
presence is not a proof of every dlopen path; no parser/RFC, native syscall,
noninterference or hardware theorem is inferred from a row or its count.
The full M1/M2 theorem and VM baselines remain regression evidence.
