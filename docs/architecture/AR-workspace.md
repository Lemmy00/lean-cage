# AR-workspace: M3 authority model, Linux realization and evidence plan

Realize [§FS-workspace](../functional-spec/FS-workspace.md#fs-workspace-m3-offline-workspace-contract-version-1) with a separate `m3/` package dependent on the preserved M2
package. This architecture begins as M3.1; subsequent packages must record actual
implementation and evidence without upgrading planned claims by implication.
[§DA-m3-profile](../decisions/architectural/DA-m3-profile.md#da-m3-profile-frozen-runtime-copied-workspace-and-distinct-run-authority) records the runtime, identity and snapshot decisions.

## runtime: Frozen input and provenance

`profiles/m3/runtime-lock.json` selects an amd64 OCI manifest by SHA-256 and records
its config, four compressed layers and four uncompressed diff IDs. The exact
upstream manifest/config bytes are adjacent files. The entire merged filesystem
is the runtime/data closure, with explicit profile overlays and mountpoints from
[§FS-workspace.filesystem](../functional-spec/FS-workspace.md#filesystem-snapshots-aliases-and-lifetime). Its 97 package records include source names, versions
and resolved copyright-notice hashes; the Python license has its own record.

The inspected upstream recipe is
[docker-library/python at 152874b](https://github.com/docker-library/python/blob/152874b138f0b1c4699fbdcb52b174608cfbfff5/3.13/slim-bookworm/Dockerfile).
Its base image digest, Python source archive hash and build metadata are provenance,
not a verified build attestation. Preserve notices from `/usr/share/doc`,
`/usr/share/common-licenses`, Python's LICENSE and bundled packages. Upstream
licenses govern runtime redistribution; the repository's Apache license does not
relicense these artifacts. Cache downloaded bytes only under `.tools/m3vm`.

Layer composition uses [OCI image-spec v1.1.1](https://github.com/opencontainers/image-spec/blob/v1.1.1/layer.md).
Verify size/hash before parsing, apply whiteouts to previous-layer entries, reject
escaping/duplicate/conflicting archive names, preserve reviewed symlinks and
resolve hard links within the artifact. Never extract through host symlinks, run
maintainer scripts, or use `ldd` on guest binaries. Before M3.3 acceptance, inspect
ELF PT_INTERP/DT_NEEDED passively and validate the required workload paths in the VM.
Optional GUI extensions are outside the supported subset, not silent additions
to the closure. Missing required dependencies fail admission/workload acceptance.

## interfaces: Portable objects, state and effect results

The planned modules are `m3/LeanCageM3/Policy.lean`, `Authority.lean`,
`Lifecycle.lean`, `Filter.lean`, `Resources.lean`, `Results.lean` and `Proofs.lean`.
Use [§AR-core.state](AR-core.md#state-extensible-state-and-effects) and [§AR-core.adversary](AR-core.md#adversary-quantify-over-hostile-execution): policy is independent of syscall flags,
while the Linux layer gives explicit ABI/effect interpretations.

State must distinguish the object graph, names/mounts, open descriptions,
descriptor tables, process/thread birth identities, per-run credentials, cgroup
membership/counters, phase, actual entry, observed entry, cancellation requests,
and released resources. Use UInt32 UID/GID/syscall words, UInt64 masks/counters,
signed 32-bit fd/pid/error representations and checked conversion to bounded
lengths/offsets. Abstract birth identities supplement, not replace, machine reuse
and lifetime obligations. A wrapped run ID cannot be reused.

Guest requests include path traversal, open/dup/close, read/write/mmap, link/unlink/
rename, fork/thread/exec, signals and denied external operations. Resolve names
to objects and preserve held handles across rename/unlink; include interleavings
between lookup, lookup failure and subsequent effects. Host/sibling steps may
modify their own objects and original input paths, attempt access and contend for
resources. They cannot be removed from the model to obtain preservation.

Effects return successful receipts, errors, interruption, reporting loss or
contract-violation outcomes. Success receipts describe the specific operation,
not the whole desired isolation invariant. Backend refinement must show concrete
effects meet these local contracts. Denied attempts remain observations/transitions.
Do not define `Step` by assuming a target safety property of its result.

## filesystem: Linux construction and handle discipline

Extend the fresh root helper in `native/leancage_m3.c`; keep M2 source unchanged.
The controller binds validated policy and prepared artifact identities to a
bounded private plan. The helper independently checks the protocol/profile before
constructing an owned mount/PID/net/IPC/UTS scope. Private mount propagation, a
read-only runtime root, private tmpfs workspace, restricted procfs and enumerated
device objects implement [§FS-workspace.filesystem](../functional-spec/FS-workspace.md#filesystem-snapshots-aliases-and-lifetime). Drop the old root and all
construction handles before guest entry. Root construction and input copying must
not delegate authority to a guest-controlled pathname or mount.

Resolve supervisor-owned directories relative to trusted held dirfds, with
no-follow/beneath/no-magic-link checks appropriate to each operation. Reject source
mutability, outside hard-link authority and special files. Guest name resolution
uses the isolated root, mount rights and credentials; it is not universally
replaced by a string-prefix or `openat2` check in the launcher. The object proof
must cover the actual guest syscall paths and surviving descriptions.

Separate stdout/stderr pipes, frozen stdin, owned cgroup and private reports are
created by the supervisor. Close every inherited alias before exec. UID allocation
and quarantine are supervisor state, outside the guest namespaces. Same-run
signals/fork/thread/exec retain scope; foreign operations require explicit denial.
The exact allowed syscall table and argument guards are owned by M3.3, including
the clone mask, architecture rejection and explicit ENOSYS fallback.

## transport: Private events and public result

Implement [§FS-workspace.results](../functional-spec/FS-workspace.md#results-entry-cancellation-and-bounded-transport) by M3.3. Use inherited private pipes whose writers
are exclusively trusted processes; close all guest copies before exec. Descriptor
ownership, proc restrictions and denied pidfd_getfd/ptrace are part of authenticity.
No unauthenticated console line participates in a decision. The initial child
error pipe is not the public result API and its EOF is not exec evidence.

Freeze a little-endian 32-byte frame header: magic `LC3R`, UInt16 version, UInt16
kind, UInt64 run identity, UInt64 sequence, UInt32 payload length, UInt32 zero
reserved field. Maximum total frame size is 65536. Kind-specific payloads encode
typed setup, entry, final status and cancellation events; M3.3 must enumerate them
before implementing the decoder. Check exact lengths, ownership/run/sequence,
reserved fields, EOF and duplicate final messages. Never deserialize a native C
struct as the protocol without explicit byte and padding handling.

The collector multiplexes trusted events, output and cancellation without waiting
for a caller to consume guest bytes. Bounded spool buffers and capture prefixes
must be outside the guest's memory limit with separate admission reservations.
Every error path attempts owned teardown and reports available knowledge. Preserve
the first observation of entry and every cancellation reason despite later races.

## resources: Concrete accounting boundary

Implement [§FS-workspace.resources](../functional-spec/FS-workspace.md#resources-units-ownership-and-failure) using a supervisor-owned cgroup v2 subtree,
initially empty and configured before the stopped first guest is attached. Init
and the controller remain outside it. No guest cgroupfs mount or writable handle
exists. Reject missing controllers, delegation conflicts, failed readback, counter
overflow and inability to attach the guest before entry.

The selected Linux semantics are in the
[pinned kernel's cgroup v2 contract](https://raw.githubusercontent.com/torvalds/linux/1253a6aa5d104312bf0992afacc15220ae35bdf9/Documentation/admin-guide/cgroup-v2.rst).
`memory.max` may be transiently exceeded; `pids.max` counts threads as tasks;
`cpu.max` limits bandwidth. None alone supplies an exact cumulative CPU deadline.
The contract separately records sampled usage, cancellation and final observations.
M3.5 must establish controller ownership, inherited placement, no escape/migration,
and extinction observations, and test lower-bound positive workloads as well as
actual limit failures. Scheduler/kernel/kill progress remain liveness premises.

## proofs: Planned declarations and nonvacuity

The following are obligations, not existing theorem names. Each requires a full
type, exact hypotheses, transitive axioms and executable source identity in the
eventual M3 assurance manifest. Preserve the complete M1 and M2 theorem baselines.

| Target declaration | Required quantification and useful witness |
|---|---|
| `validate_iff` | All bounded policy bytes; accepted exactly when shape, artifact references and bounds are valid; example request accepted, malformed/unknown input rejected |
| `reachable_authority` | Every reachable interleaving of guest, sibling and environment effects; guest authority cannot expand into protected classes; shell/Python read/write trace exists |
| `guest_preserves_protected` | Every guest-origin step preserves protected object contents/ownership, including previously opened aliases; host-origin changes remain explicit |
| `descendant_inherits` | Every fork/thread/exec preserves actual run credentials, root, handles, filter and cgroup; multithreaded and orphan witnesses |
| `policy_filter_action` | Arbitrary UInt32 arch/syscall and UInt64 argument words; actual generated bytecode matches reviewed allow/deny/ENOSYS decisions, no sampled-input proof |
| `entry_requires_receipts` | Every actual entered state has completed setup including mounts, limits, descriptors, privileges and filter; failed setup has no successful continuation |
| `private_report_knowledge` | Every accepted frame derives from owned transport; arbitrary guest byte streams cannot alter outcome; short/lost/forged-message witnesses |
| `cancel_not_completion` | Requests preserve possible live members/entry races; cleanup complete requires observed extinction and release; natural exit/cancel witnesses |
| `resource_scope` | Every guest task is in the configured scope; separate charged-memory/bandwidth/sampled-budget statements with precise kernel-effect premises |
| `lifecycle_projection` | Erase workspace/resource preparation and project successful operation ordering/entry/teardown into the M2 lifecycle event abstraction |

The last projection is deliberately limited. M2 hardcodes UID 65534, scope 1,
sealed static images and the old decoder; M3 uses distinct IDs, a runtime closure
and another filter. Reusing an M2 event-order lemma does not prove the stronger
M3 authority/credential/image invariant. Prove those independently over actual M3
state, or derive explicitly parameterized lemmas without changing old statements.
Provide inhabitable success and denial/error/race executions. Partial correctness
does not assert successful progress, fairness or kernel-call termination.

## correspondence: Additional open M4 boundaries

These extend [§AR-lifecycle.correspondence](AR-lifecycle.md#correspondence-m4-obligation-ledger). None is closed by artifact inspection,
source mapping or VM tests. M2's eight entries remain open.

| Key | Source/effect boundary | Dependent property | Closure required |
|---|---|---|---|
| M4-m3-policy | JSON/UTF-8/integer parsing, input store and native plan | Accepted requests match proved values | Parser/serialization and C/Lean runtime relation |
| M4-m3-filesystem | archive/tree materialization, mount/pivot, VFS lookup, open/link/rename/mmap/proc/devices | Actual object authority and race/alias behavior | C memory and pinned Linux VFS/mount/descriptor effects |
| M4-m3-loader | initial ELF, PT_INTERP, ld.so, dlopen, shebang/Python import, later exec | Code loading adds no ambient authority | Loader/runtime/FFI and executable correspondence |
| M4-m3-identities | UID leases, PID reuse, ptrace/proc/signal and inherited handles | Sibling and supervisor separation | Concurrent kernel credential/process/handle relation |
| M4-m3-filter | emitted instruction bytes, arg widths, clone flags, kernel BPF | Reviewed policy-to-filter action | Bytecode compiler, ABI and interpreter/JIT correspondence |
| M4-m3-resources | cgroup writes/readback/attach/accounting/kill, tmpfs | Scope, limits and cleanup | Kernel accounting with delays/overshoot and scheduling premises |
| M4-m3-results | event pipes, framing, output buffers and exporter | Entry knowledge and authorized disclosures | Concurrent native protocol/parser and filesystem relation |
| M4-m3-artifacts | runtime layers, overlays, helper/controller/compiler and guest image | Deployed bytes implement reviewed sources | Reproducible identity chain plus executable proof, not hashes alone |

## experiment: Bounded first native-semantics connection

Use [CompCert 3.18](https://github.com/AbsInt/CompCert/tree/14d616046360a0b2611ebdfc2f98368af402e1f7)
Clight small-step semantics as the candidate C boundary. Its explicit memory and
integer model and external calls are the reason for selection; see the upstream
[Clight semantics](https://compcert.org/doc/html/compcert.cfrontend.Clight.html) and
[C subset contract](https://compcert.org/man/manual005.html). Pin any experiment's
Rocq/frontend tooling separately before running it; do not change Lean/Lake pins.
Review upstream licensing before vendoring or redistributing tooling.

Before expanding the native helper, isolate the actual bounded operation dispatcher
and terminal-failure/report-framing slice, at most 300 authored C lines, with
explicit syscall/effect stubs. Include short reads/writes, EINTR, invalid operation
bytes, signed errno conversion, pointer bounds and overflow. Retain the real branch
order and control/data dependencies. Produce an identified Clight AST and attempt
a simulation to the portable operation/error trace for arbitrary input bytes and
effect outcomes, with no undefined behavior under stated buffer ownership.

Deliver source/AST hashes, full proposition and premises, proof-tool/check command,
success/failure witnesses and an explicit mapping to Lean's event definitions.
A Rocq proof is not a Lean theorem: either check a bridge or retain that connection
as open. External stubs cannot assert successful containment or hide errors.
This experiment does not certify the existing GCC executable or Linux effects.

Replan before native expansion if the actual slice cannot be represented without
assuming its conclusion, erasing asynchronous failure, treating pointer-based
effects as arbitrary success, or replacing production code with an unconnected
toy. Record unsupported C/FFI/concurrency constructs and a revised semantics or
smaller maintainable native boundary. The finite experiment is an M4 feasibility
gate, not a commitment to prove an entire kernel/compiler during M3.

## ownership: Package files and shared interfaces

No parallel editing is assigned. Ownership below names work packages and establishes
interfaces before implementation; it does not authorize delegation.

| Package | Owned implementation/evidence | Interface and exit |
|---|---|---|
| M3.1 | This contract family, `profiles/m3/*`, acceptance matrix, assurance/roadmap | Versioned authority, runtime, policy and knowledge/limit contracts |
| M3.2 | `m3/LeanCageM3/Authority.lean`, `native/leancage_m3.c` filesystem functions, `scripts/m3_runtime.py`, filesystem VM fixtures | Private frozen root/workspace, object/effect model, source map and alias/failure evidence |
| M3.3 | `Policy.lean`, `Filter.lean`, `Lifecycle.lean`, `Results.lean`, `m3/Main.lean`, native filter/transport, runtime fixtures | Validated plan, dynamic runtime, proven filter action and private reporting before guest entry |
| M3.4 | Authority/process/channel proof additions and network/IPC/peer fixtures | Explicit denied operations plus capable positive controls and sibling attempts |
| M3.5 | `Resources.lean`, native cgroup/supervision, limit/cancel fixtures | Named counters and overshoot, scoped placement, owned cleanup and failure behavior |
| M3.6 | `m3/LeanCageM3/API.lean`, check/run/report interface and schemas | Private framed transport to typed API; bounded streams/artifacts and assurance report |
| M3.7 | `Proofs.lean`, `scripts/audit_m3.py`, query/gate, `scripts/run_m3_vm.py`, `tests/m3/*`, `assurance/m3-*`, handoff | Full statement/axiom audit, fresh source-bound VM evidence and regression/claim review |

Coordinate modifications to `scripts/check.sh`, Grund guidance, the assurance
register and source fingerprints at package gates. Preserve old theorem manifests,
M1/M2 native code, dependency/toolchain pins, VM configurations and raw evidence.
M3 gets its own image/config/evidence identities. Historical evidence validation
must support a moved checkout and reject mixed roots or stale source identities.

## acceptance: Coverage and handoff gate

`docs/reviews/M3-acceptance.md` maps allowed/denied operations, failure boundaries,
interference and races to proposed theorem obligations and VM cases. Every VM case
must record a private typed result, expected output/artifact observation, owned
scope extinction and survival of unrelated sentinels where applicable. A timeout,
missing kernel mechanism or failed harness is infrastructure failure, not denial.

Run Grund formatting and the existing full gate for M3.1. As implementation grows,
extend the gate with the M3 package, complete type/axiom inventory, policy/runtime
lock checks, native compilation and archived evidence checks. Explicit VM replay
alone runs workloads. Final M3 acceptance requires new replay/artifact evidence,
useful workloads and every residual assumption in [§FS-assurance.evidence](../functional-spec/FS-assurance.md#evidence-required-claim-record).
