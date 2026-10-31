# M3 acceptance matrix

This is the executable-test plan for [§FS-workspace](../functional-spec/FS-workspace.md#fs-workspace-m3-offline-workspace-contract-version-1) and [§AR-workspace.acceptance](../architecture/AR-workspace.md#acceptance-coverage-and-handoff-gate),
not a record of passing M3 workloads. Names below are stable case/obligation targets.
The contract baseline is M3.1; fill in actual results only after each package's gate.
All hostile workloads run in the designated disposable VM.

| Case group | Allowed/control execution | Denied, failure or race execution | Proof obligation / owner |
|---|---|---|---|
| policy | Frozen example; exact bounds | Unknown/duplicate fields, noninteger/overflow, invalid UTF-8/NUL, long argv, unsupported profile or digest | `validate_iff`; M3.3 |
| snapshot | Frozen directories/regular files; repeated blobs copied independently | Bad hash/size, duplicate paths, dot-dot, links/special files; source changes after snapshot | `reachable_authority`; M3.2 |
| runtime | Exact shell/Python, loader and data reads | Runtime write/chmod/unlink/mmap, stale digest, replaced loader/config, missing dependency | `entry_requires_receipts`, `guest_preserves_protected`; M3.2–3 |
| workspace | Read/write/create/remove, executable script/native file | Traversal to host/sibling; concurrent external source rename/write; outside inherited aliases | `reachable_authority`; M3.2 |
| aliases | Internal symlink/hard-link, held fd after unlink | Cross-root links, dirfd/cwd/proc magic link, rename-vs-open, runtime write alias | `guest_preserves_protected`; M3.2 |
| mounts | Correct private root and workspace | Failed pivot/mount/remount, shared propagation, old-root handle, mount/setns/unshare attempt | `entry_requires_receipts`; M3.2–3 |
| proc_devices | Own PID view, null/zero/urandom, own fd links | Host/global proc, init memory/fds, raw devices, mknod, sysfs/cgroupfs | `reachable_authority`; M3.2–4 |
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

Each row can expand into multiple cases. A denied attempt must name its expected
errno/signal/result and demonstrate that the equivalent mechanism works in a
trusted isolated peer where appropriate. A failed workload or unavailable feature
does not satisfy denial. Injected faults are labeled separately from observed
ordinary behavior. Tests/source maps do not discharge [§AR-workspace.correspondence](../architecture/AR-workspace.md#correspondence-additional-open-m4-boundaries).

The final review must state theorem types and assumptions, exact counters and
artifact hashes, useful witnesses, all unimplemented/unchecked rows, and whether
the reusable check/run/report interface actually exercises the same helper. The
M2 handoff, 445 M1 declarations and 274 M2 declarations remain regression baselines.
