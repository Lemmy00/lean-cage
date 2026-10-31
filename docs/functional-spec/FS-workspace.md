# FS-workspace: M3 offline workspace contract, version 1

This contract specializes [§FS-policy.authority](FS-policy.md#authority-resources-and-permitted-operations), [§FS-isolation.filesystem](FS-isolation.md#filesystem-object-level-confinement),
[§FS-isolation.interference](FS-isolation.md#interference-concurrency-and-environment), [§FS-resources.limits](FS-resources.md#limits-precise-semantics) and [§FS-observations.logical](FS-observations.md#logical-functional-observations).
It defines `linux-x86_64-offline-workspace-m3-v1`. The implementation is in `m3/`
and `native/leancage_m3.c`; checked claim and acceptance status are recorded in
[§FS-assurance.workspace](FS-assurance.md#workspace-m3-workspace-model-and-vm-evidence). Model proofs and VM tests do not establish native/Linux
correspondence.
The M2 lifecycle evidence remains [§FS-assurance.lifecycle](FS-assurance.md#lifecycle-m2-lifecycle-and-filter-semantics-claim-record).

## profile: Supported environment and useful workloads

Use the M2 fresh root controller/helper and initial user namespace, inside a
disposable x86-64 Linux VM. No setuid installation, host bind mounts or host guest
execution is supported. The named kernel baseline is Linux 6.18.59 with a separately recorded M3 configuration adding file locking and shebang
execution.
Kernel features must be checked, not inferred from the version string.

The runtime is the exact Linux/amd64 root filesystem identified by
`profiles/m3/runtime-lock.json`: Dash 0.5.12-2, CPython 3.13.18, its ELF loader,
libraries, standard library and data. All ordered image layers are inputs, even
files outside the tested workload subset. A tag, host `/usr`, package update or
runtime download at launch cannot substitute for these bytes. OCI is an artifact
format here; no Docker daemon or container runtime is part of the execution design.

Required useful executions are shell pipelines/redirection and child exit status;
Python UTF-8 text/JSON processing, directory traversal, file replacement and
hashing; imports from the workspace; `subprocess` invoking the pinned shell or
Python; and threads followed by supported fork/exec. Scripts, native x86-64 code,
and imported modules are untrusted. Their behavior need not cooperate with limits.
GUI/Tk, interactive terminals, package installation as a service, network clients,
user namespaces, arbitrary devices, other ABIs and caller-selected mount layouts
are unsupported. Presence of a tool or module in the archive does not advertise
compatibility for every operation it offers.

## policy: Bounded typed request

`profiles/m3/policy.schema.json` and `example-policy.json` fix the request shape.
The parser accepts at most 65536 UTF-8 bytes, rejects duplicate keys,
unknown fields, floats/exponents for integer fields, malformed UTF-8, embedded
NUL, overflow and trailing input. All fields are required; there are no silent
defaults. Schema validation is necessary but not sufficient for admission.

The request identifies one profile, one locked runtime digest, an optional
workspace-input digest, optional stdin digest, an argument vector, limits and an
export choice. Digests identify artifacts in a trusted prepared-input store;
they do not grant a host path or an arbitrary inherited file descriptor. Admission
must verify byte identities, ownership, bounds and platform support. An unknown
digest or unavailable mechanism produces `rejected` before guest entry.

`argv` has 1–64 nonempty UTF-8 strings, each at most 4096 encoded bytes, with a
combined encoded size including NUL terminators at most 16384 bytes. `argv[0]` is
exactly `/bin/sh` or `/usr/local/bin/python3`; subsequent guest exec is not limited
to these two names. Cwd is `/workspace`. Initial environment is exactly
`PATH=/usr/local/bin:/usr/bin:/bin`, `LANG=C.UTF-8`, `LC_ALL=C.UTF-8`,
`HOME=/workspace`, `TMPDIR=/workspace/.tmp`, `TZ=UTC`,
`PYTHONDONTWRITEBYTECODE=1`, `PYTHONNOUSERSITE=1`. No caller environment is inherited.
These startup settings are convenience, not a restriction on subsequent guest code.

## authority: Objects and rights

An object identity includes its owning run and allocation generation; a pathname,
descriptor number, inode number or PID alone is not an authority identity.

| Object class | Guest authority | Required boundary |
|---|---|---|
| Locked runtime objects and public configuration | Read, search, executable mappings and execution | No write, metadata change, replacement, extra mount alias or writable inherited handle |
| Private workspace objects, including `.tmp` | Read/write/create/remove/rename; internal links; mappings and execution | All aliases resolve within this run's authority; no live host/sibling backing object |
| stdin snapshot and stdout/stderr pipes | Read stdin; write designated output endpoints | No descriptor grants to a host file, terminal, socket or private report channel |
| Same-run anonymous pipes, memory and descendants | Communicate, fork, thread, exec, wait and permitted signals | Scope and restrictions inherited; no migration out of the owned scope |
| Minimal procfs and device views | Only the enumerated facilities below | No host process view, supervisor memory/handles, control files or ambient devices |
| Host, sibling, supervisor and input-store objects | None, except explicit public inputs/output delivery | Remain protected under guest steps and permitted concurrent interference |

Runtime bytes and metadata are public. The workspace and stdin are private to the
run and its authorized caller, but fully readable by its own hostile guest.
A guest can deliberately disclose any of its input through authorized output.
Sibling workspaces, caller files not imported, report endpoints, runtime writers,
credential allocator and cgroup controls are protected objects.

Each concurrent run receives a distinct UID/GID pair reserved by the trusted
operator, absent from ordinary host/sibling processes. All real/effective/saved/
filesystem IDs agree, supplementary groups and all capability sets are empty,
and NNP persists. IDs are UInt32, with 0 and 65534 excluded. The VM allocation pool
is 100000–100999, with exhaustion rejected. Reuse waits for scope extinction and
release of every run-owned object/handle. This versions M2's fixed UID 65534;
its credential theorem cannot directly establish M3 sibling isolation.

## filesystem: Snapshots, aliases and lifetime

Input is a frozen content-addressed tree, not a live directory binding. The
`leancage-input-tree-v1` manifest lists UTF-8 relative path components, directories
and regular-file blob digests/sizes. Empty, dot, dot-dot, slash-in-component, NUL,
duplicate and conflicting entries are rejected. No symlinks, hard-link records,
devices, sockets, FIFOs, sparse extents, xattrs, ACLs or ownership requests enter
through this import format. Repeated blob digests become independent copied files.
The caller's conversion of live files to this snapshot is outside the launch;
the snapshot identity, rather than an asserted atomic view of a changing source
directory, is the accepted input. The helper validates all content before entry.

The exact manifest bytes begin with `LCTREE1\n`, followed by newline-terminated
records `D HEXPATH` or `F EXEC HEXPATH SIZE SHA256`. Fields use single spaces;
`EXEC` is `0` or `1`, size is canonical decimal, and hex uses lowercase. Paths
decode to UTF-8, at most 4095 bytes, at most 64 components of at most 255 bytes;
parents precede children. `.tmp` and its descendants are reserved. The manifest
is at most 4 MiB; its SHA-256 is the request's tree identity. The root-owned input
store contains `trees/DIGEST` and `blobs/DIGEST`, with regular files only. Blob
contents are checked while copying to new objects; no source handle reaches the
guest. Stdin is likewise copied, hashed and sealed before entry.

Materialize runtime and workspace on separate private filesystems. Runtime remains
read-only, root owned and `nosuid`; workspace remains guest owned and `nosuid,nodev`,
with executable files allowed. The guest root contains no host root alias.
`/tmp` and `/var/tmp` resolve to `/workspace/.tmp`; `/run` is empty and read-only.
Private fixture passwd/group/hosts/hostname/resolv.conf replace image defaults;
no host names, DNS settings, machine ID or credentials are copied. Shared mount
propagation is disabled. All construction handles outside the intended root are
closed before entry, including aliases inherited on stdin/stdout/stderr.

Guest symlink/hard-link/rename/open-unlink races remain transitions, including
attempts using cwd, dirfds, procfs magic links, open-by-handle, executable mappings
and concurrently replaced names. Cross-filesystem links cannot grant a runtime
write; no textual-prefix argument suffices. The model accounts for existing file
descriptions and mounts after names disappear. No host writer can modify private
runtime/workspace objects during a run. Ordinary processes may change the original
source tree, contend for resources and attack access boundaries concurrently.
Trusted root reconfiguration remains an explicit environmental exclusion.

The private procfs is restricted to the owned PID namespace with global views
excluded (`subset=pid`) and restricted process visibility (`hidepid=2`). Same-run
proc links may alias only already granted guest objects; syscall controls deny
ptrace, process-memory access and pidfd descriptor acquisition. Trusted init has
no guest-readable memory/descriptor view. `/sys`, cgroupfs, host procfs, POSIX/SysV
IPC mounts and device trees are absent. `/dev` contains only null, zero and urandom
plus fd/stdin/stdout/stderr links into that procfs. Random bytes are explicit
nondeterministic input; raw devices, PTYs and device creation are unsupported.

Workspace exists from materialization until teardown. Export occurs only after
observed guest extinction, using stable owned directory handles. `discard` exports
nothing. `regular-files` exports directories and regular-file bytes into a new
bounded content-addressed result, without writing back to the caller's input.
Symlinks, devices, sockets and FIFOs are recorded as omitted and never followed;
hard links are flattened. Raw guest filename bytes are encoded in the result, not
interpreted as destination paths. Bounds or read errors produce `export_failed`,
never a silently complete partial export. Runtime and workspace mounts are then
released; a missing cleanup observation prevents a completed result.

Export uses `LCEXPORT1\n` and the same directory/file records, plus `O HEXPATH`
for omitted objects. Export paths encode raw bytes, without the input UTF-8
restriction. Each regular-file name gets a separate copied blob, including hard
links; the manifest records the digest. Total copied bytes are bounded by the
workspace capacity, entries by its inode limit and manifest bytes by 16 MiB.
Flattened hard links can exceed those bounds and fail export. A failed export
keeps any partial artifacts explicitly incomplete. Neither export failure nor
an omitted object rewrites the observed guest termination.

## execution: Dynamic code and channel restrictions

The initial shell/Python executable, ELF interpreter, shared libraries, loader
configuration and standard-library data resolve only within the immutable runtime.
Initial executable identity records the manifest and resolved content digest.
After entry the guest may execute workspace code and replace its own programs;
no claim binds every later exec to the initial digest. Loader searches, `dlopen`,
scripts and Python imports confer no rights beyond [§FS-workspace.authority](FS-workspace.md#authority-objects-and-rights).

Use a distinct `m3-offline-v1` syscall policy and bytecode contract. Preserve the
exact M1 decoder and M2 static/sealed profile. The M3 contract denies non-x86-64 and
x32 entry, privilege/namespace/mount changes, tracing and foreign-process memory,
network and Unix sockets (including socketpair and descriptor passing), SysV IPC,
keyrings, BPF/perf, io_uring, kernel/module/reboot operations and other unlisted
syscalls. Same-run pipes and signals remain useful. Explicitly reviewed exceptions
such as `clone3 -> ENOSYS` may permit a pinned libc fallback; they cannot return
allow. Argument-pointer contents are not inspectable by classic seccomp BPF.

M3.3 must enumerate every allowed syscall/argument form and prove its generated
filter action, including multithreaded clone/fork/exec. Unknown calls fail closed.
Path confinement comes from object/mount/credential contracts; the filter alone
cannot prove it. M3.4 supplies independent in-VM network/IPC/foreign-process peers
and positive controls, so missing functionality is never counted as denial.

## resources: Units, ownership and failure

All limits apply to the entire guest descendant/thread scope. The trusted
controller and namespace init remain outside guest-controlled budgets. Preflight
requires a root-owned cgroup v2 subtree with memory, pids and CPU controllers;
the guest gets neither delegation nor cgroup descriptors. Admission places the
stopped first guest into the configured empty group before any untrusted step.
No later inward migration, limit reduction or scheduler-class escape is supported.

| Request field | Meaning and selected mechanism | Limit behavior and claim boundary |
|---|---|---|
| `memory_max_bytes` | Page-aligned charged-memory limit, `memory.max`; swap disabled, group OOM enabled | Allocation may fail or OOM may kill. This is the named Linux accounting limit, not exact RSS or an instantaneous all-memory ceiling; transient excess has no promised numerical bound |
| `tasks_max` | Maximum guest tasks, including threads, via `pids.max` | Further creation fails; trusted init excluded. No extra task is admitted through migration |
| `cpu_quota_us` / `cpu_period_us` | Aggregate fair-scheduler CPU bandwidth via `cpu.max`; burst set to zero | Throttling, not a cumulative runtime budget or minimum progress guarantee |
| `cpu_budget_us` | Cumulative `cpu.stat usage_usec` since guest admission | Trusted sampling requests cancellation at/above threshold; report final usage and observed overshoot |
| `wall_time_ms` | Monotonic duration from the recorded release attempt for the stopped first guest | Deadline requests cancellation; it does not itself prove extinction |
| `workspace_max_bytes` / `workspace_max_inodes` | Private tmpfs capacity/inode bounds including imported files and `.tmp` | ENOSPC is a permitted guest result; separate from charged memory and bounded export |
| `stdin_max_bytes` / `stdout_max_bytes` / `stderr_max_bytes` | Total input/captured output bytes | Oversized input rejects; first output byte beyond a cap triggers cancellation and a truncation flag |

Memory excludes charges retained by other cgroups, including preloaded runtime or
imported pages. Supervisor admission reserves those separately using the locked
runtime size and workspace capacity. The VM allocator serializes a 1536 MiB active reservation ledger. Each run
reserves its requested charged-memory limit, workspace capacity (twice for
export), stdin cap and 16 MiB of supervisor working allowance. The remaining
512 MiB is the fixed runtime/kernel/supervision allowance in the 2048 MiB VM.
Insufficient reservation or an unreadable/quarantined reservation rejects new
admission. Release occurs only with the UID lease after observed extinction and
teardown. This is admission accounting, not a hard physical memory guarantee;
retained result artifacts belong to the caller and require separate provisioning.
No aggregate host-memory guarantee follows.
The selected accounting semantics and any transient overshoot must appear in the
report. Requests for strict zero-overshoot memory, cumulative CPU or deadline
ceilings are unsupported. Clock/scheduling/accounting/delivery delays have no
finite unconditional bound; conditional bounds require named, measured premises.

The target CPU/deadline polling interval is 10 ms; lateness is reported, never
assumed absent. Setup has a separate 30000 ms watchdog. A fatal alarm covers preparation before
the collector exists; that loss yields unknown outcome/cleanup and quarantine.
The collector then uses monotonic polling with the same
cancellation/unknown semantics. Cancellation kills the owned cgroup and PID scope,
then observes both extinction and reaping. OOM evidence requires a private sampled
counter increase, not just SIGKILL. Pids or workspace denial does not force failure
if the guest handles it. Counter read failures, impossible values or overflow
cause supervisory cancellation and an unknown accounting result. M3.5 must test
each condition, preserve unrelated peers and document supervision capacity/fairness.

## results: Entry, cancellation and bounded transport

The result is `leancage-result-v1` with independent typed fields: `entry = no | yes |
unknown`; `termination = rejected | setup_failed(stage, errno) | exited(UInt8) |
signaled(UInt32) | cancelled | unknown`; `cleanup = complete | pending | unknown`;
and `export = discarded | complete(digest) | failed(reason) | unavailable`.
It also records all observed cancellation triggers, leader status if known, limit
observations and final accounting, output counts/truncation, policy/runtime/filter
identities and the source/artifact/profile assurance record. Errnos are positive
Int32 values; zero is never an error. A natural exit racing cancellation may have
an exit status and a cancellation request; observed history is not overwritten.

Entry becomes yes only after trusted exec observation; missing/partial error
messages or a guest printing success never establish entry. Cancellation request
is not cancellation completion. A completed invocation requires scope extinction,
reaping, closed private handles, finished/discarded export and mount/cgroup release.
Unknown entry/termination does not prevent independently established cleanup;
unknown cleanup prevents identifier/resource reuse and requires quarantine.

Three byte streams (stdin/stdout/stderr) and private control/result frames are
distinct channels. Only trusted controller/helper/init hold result write endpoints;
they are absent from every guest descriptor table and protected from proc/pidfd
reacquisition. Guest stdout/stderr are arbitrary bytes, including forged frames
and console markers. They are never parsed as control messages. M3.3 implements
this separation before accepting shell/Python workloads; M3.6 provides the API.

Captured output is a bounded prefix with no implied ordering between stdout and
stderr. The trusted collector services both streams while supervising, retaining
at most their declared caps plus fixed bounded buffers. A slow caller may cause
guest pipe backpressure; it cannot block cancellation or result collection.
After an output cap is exceeded, cancel and drain/discard until extinction;
report transport loss or storage failure as such. Partial, duplicate, oversized,
out-of-order or absent private frames yield unknown knowledge and cleanup efforts.
An unavailable result channel never fabricates success, failure-before-entry or
cleanup completion. Public result framing has a 65536-byte cap; export data and
guest bytes use separate bounded artifacts/streams.

Saving an already decoded public report is a separate operation. Its failure
must retain the observed entry, termination, cancellation and cleanup fields.
The public JSON adds `report_storage = stored | failed | not_applicable` and
`report_storage_error` (null or a diagnostic). Publish stored reports by atomic
rename after a complete write; never expose a partial report as the saved result.
A storage failure makes the command exit 126 while preserving the actual guest
outcome in its JSON. Preflight and results without an allocated run use
`not_applicable`. Retrieval is available only after successful publication.

Accounting failures produce null usage/peak/event/elapsed/overshoot fields in the
public report. Output-storage failure produces null observed/captured byte and
truncation fields; a partial file is not reported as a complete capture.

## observations: Public information, secrets and proof boundary

Public inputs are the profile/runtime/policy shape and declared limits, provided
argument bytes, public fixture configuration and the intended observation schema.
Workspace/stdin contents and caller-private object identities are private inputs;
their digests are visible only to the authorized caller/supervisor. Public-to-guest
does not mean public-to-siblings. The authorized caller receives output prefixes,
selected workspace export, typed outcomes, entry/cleanup knowledge, accounting,
limit/cancellation events, errors and timing. Termination is observable. Siblings
may observe their own behavior, public runtime and resource contention, never an
authorized copy of another run's output or private result.

The intended safety theorem ranges over all reachable object/effect executions,
including guest races, permitted host/sibling steps, failures and reporting loss.
It must show non-expansion of object authority, inherited descendant restrictions
and preservation of protected object contents, with useful allowed witnesses.
Such a theorem is not noninterference: Linux global observations and allocation,
timing, cache, scheduling and speculation channels remain explicit obligations.
No functional confidentiality or native correspondence result is asserted. The destination
[§FS-observations.hardware](FS-observations.md#hardware-software-observable-channels) and the stronger-claim rules [§FS-assurance.closure](FS-assurance.md#closure-rules-for-stronger-claims) remain.
