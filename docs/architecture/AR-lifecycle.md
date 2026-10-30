# AR-lifecycle: M2 controller, native helper and evidence

Implement [§FS-lifecycle.model](../functional-spec/FS-lifecycle.md#model-executable-controller-and-effect-contracts) and [§FS-lifecycle.profile](../functional-spec/FS-lifecycle.md#profile-supported-entry-and-privilege-boundary) with a separate Lake package
under `m2/`, depending on the unchanged root M1 package. This keeps the original
M1 modules, native driver, configuration and raw VM record reproducible. Shared
handoff documentation and the top-level gate may grow with reviewed fingerprints.

## design: Executable boundary reviewed before native implementation

The Lean executable reads a bounded filter, invokes M1's actual decoder, and emits
the fixed `12345678` plan only after acceptance. It execs a fresh static C helper;
there is no C override of a proved Lean definition. The helper independently
validates the plan and materializes the one decoded program tag as a fixed native
instruction table. The C/Lean table correspondence is reviewed, source-bound and
VM-tested, and remains an M4 proof obligation. Its single-threaded startup eliminates
inherited Lean runtime/allocator state. C drives the same fixed operation order;
the native interpreter rejects changed/extra/missing operations. The pre-exec
tail is no-new-privileges, seccomp, execveat, with no optional operation in between.
This deliberate M2 handle-based exec refines the portable M1 event sequence;
it does not alter M1's path-based native binding contract.

The assigned files are the new `m2/` package, `native/leancage_m2.c`, `tests/m2/`,
M2 audit/replay tooling and records, and these lifecycle/decision/assurance/roadmap
documents. Root M1 declarations and VM sources remain owned by the baseline.
No parallel editing or agent delegation is needed.

## entry: Disposition of every M1 entry premise

| M1 premise | M2 treatment | Concrete boundary |
|---|---|---|
| Dedicated trusted child before guest | Establish | Fresh helper exec, owned namespace init, forked child, exec observation |
| Single thread, no runtime locks | Establish | Single-threaded static helper; post-fork native syscall-only setup |
| Stable filter/native storage | Establish | Actual Lean decoder, single fixed program tag, reviewed canonical C table, private stack copies |
| Stable executable/path | Establish/version | Bounded copied and sealed memfd; execute checked handle, no path relookup |
| Private argv/environment | Establish | Bounded copied fixture argument, fixed argv/environment/cwd |
| No shared writers/aliases | Establish for private objects | Seals, process-private plan/filter, descriptor allowlist; trusted source snapshot intent retained |
| No inherited hostile handlers | Establish | Mask before fork, reset all 64 dispositions, explicit unmask |
| No hostile tracer | Validate/reject; retain root trust | Preflight TracerPid=0; trusted init becomes the sole tracer before setup |
| No existing seccomp | Validate/reject | Fresh self-status PID/TracerPid/Seccomp and PR_GET_SECCOMP checks; masked-query denial test; no composition fallback |
| Other preparation complete | Establish | Namespace/mount/handle/group/UID/GID/capability receipts before M1 segment |
| No arbitrary descendant behavior | Replace | Explicit hostile fork/exec/session steps; PID namespace lifetime and extinction |
| No cancellation/report ambiguity | Replace | pidfds, actual death observation, exec event and typed unknown results |
| Trusted OS/host administration | Retain with reason | Root can replace kernel/images and ptrace any process; M4/Linux and deployment trust |

## effects: Source-to-effect and failure map

| Plan operation | Native owner and effects | Failure/guest boundary |
|---|---|---|
| 1 bootstrap | Helper profile/ELF/snapshot/seals/parent pidfd/signals | No namespace/guest exists on rejection |
| 2 namespaces | Helper clone PID/mount/IPC/net/UTS; init private mounts/proc | Init reports errno; no untrusted fork before success |
| 3 handles | Guest dup allowlist to 0..4, close_range(5,UINT_MAX) | Partial changes terminal, owned init kills/reaps |
| 4 credentials | Guest bounding/ambient/groups/setresgid/setresuid/capset | Validate real/effective/saved/fs IDs, groups and capabilities; all failures terminal |
| 5 validate | Guest rechecks filter/profile receipts; tracer handshake already complete | Existing filter/changed plan rejected |
| 6 no-new-privileges | Guest prctl | Actual errno, EINTR terminal |
| 7 install | Guest prctl exact 9 instructions | No fallthrough on failure |
| 8 exec | Guest execveat(3,"",...,AT_EMPTY_PATH) | Guest possible only on image replacement; PTRACE_EVENT_EXEC witnesses it |

Init uses an error-only CLOEXEC pipe for setup and a separate framed report pipe
to the helper. Only trusted code owns report writers. It observes TRACEEXEC and
continues signal-delivery stops. On leader exit it kills namespace members and
reaps all; the helper waits on the exact init and can signal only its pidfd.
Parent-death arming is paired with pidfd readiness to close the pre-arming race.
Main passes its UInt32 PID before spawning. The helper checks the expected
parent both before and after pidfd acquisition, then arms parent death and polls
the original pidfd. Namespace init inherits its helper-parent pidfd before clone.
Tests cover controller death before helper arming and helper death before init
arming, so adoption by VM PID 1 cannot become a new successful entry premise.
The external supervisor uses signalfd and a monotonic cancellation deadline.

Only the first exec observation sends READY; later leader re-execs remain valid
and retain restrictions. Cancellation returns a completed result only after the
owned init is reaped with SIGKILL. A normal init exit and complete valid report
win a concurrent cancellation race. Missing reporting preserves unknown entry
unless an earlier trusted exec event was received. Guest exit codes never select
setup failure, including guest exit 125.

Binding references are the Linux man-pages for
[ptrace exec events](https://man7.org/linux/man-pages/man2/ptrace.2.html),
[PID-namespace init teardown](https://man7.org/linux/man-pages/man7/pid_namespaces.7.html),
[parent-death arming and credential resets](https://man7.org/linux/man-pages/man2/PR_SET_PDEATHSIG.2const.html),
and [handle-based exec](https://man7.org/linux/man-pages/man2/execveat.2.html).
The pinned source's `kernel/pid_namespace.c:zap_pid_ns_processes` waits for the
namespace's processes before init reaping. These are reviewed effect contracts,
not Lean proofs of the kernel implementations.

## vm: Separate capable disposable profile

`leancage-m2-linux-6.18.59-root-v1` reuses the checksum-pinned upstream Linux
archive and extracted QEMU/bootstrap tools from M1, in a separate `.tools/m2vm`
source/build tree. The resolved M2 configuration enables PID/mount/IPC/network/UTS
namespaces, SysV IPC, Unix/IPv4 sockets, cgroup v2 memory/pids/CPU controllers,
ptrace, memfd sealing, procfs and seccomp. CONFIG_USER_NS stays disabled for the
chosen root-helper profile. The VM has no host filesystem mounts, disks or NIC;
its guest network stack is present and positively tested. Root PID 1 runs tests
and an unrelated sentinel process. Guest code runs only as UID/GID 65534.
The M1 configuration and evidence remain unchanged. Kernel builds use two
low-priority jobs and all downloaded/generated artifacts stay project-local.

## proofs: Conditional model safety and filter semantics

`m2/LeanCageM2/` contains the executable plan/model, lifecycle invariant proofs,
and the bytecode semantics/theorems required by [§FS-lifecycle.filter](../functional-spec/FS-lifecycle.md#filter-general-action-of-the-preserved-m1-program). Its own
auditor enumerates every module/theorem, checks full types and transitive axioms,
and preserves all M1 statements against a reviewed baseline. Allowed logical
axioms remain propext, Classical.choice and Quot.sound. Native/Linux effects are
contracts, not new Lean axioms. Nonvacuity includes a complete success and hostile
fork/exec/exit/cancel traces. Failure tests cover real erroneous syscalls as well
as explicit deterministic fault injection, labeled separately in the evidence.
Hash `m2/lean-toolchain` as well as the root pin and reject a different M2 pin
before building or querying its theorem environment.

## correspondence: M4 obligation ledger

| Key | Concrete boundary | Invariant supported | Status |
|---|---|---|---|
| M4-controller | Lean IO/process exec, plan serialization, helper dispatch | Only decoded fixed plans run | Open native/runtime refinement |
| M4-snapshot | pread/write/memfd/seals/ELF arithmetic/execveat | Stable checked executable and bounded input | Open C memory/ABI and Linux refinement |
| M4-bootstrap | signal mask/actions, fork/clone, descriptor duplication/close_range | No inherited handler or authority | Open C/runtime and syscall refinement |
| M4-credentials | cap/group/UID/GID/NNP transitions and inheritance | No guest privilege recovery in initial user namespace | Open Linux credential semantics |
| M4-namespaces | clone/mount/procfs, no user namespaces | Owned process scope and observations | Open Linux namespace refinement |
| M4-filter | byte copy, sock_fprog layout, seccomp interpreter/JIT | Canonical bytecode action persists | Model semantics proved; native/Linux mapping open |
| M4-supervisor | ptrace exec/signal/wait, pidfd, parent death, report framing | Entry knowledge and descendant teardown | Open race, kernel and C semantics refinement |
| M4-artifacts | toolchain, static libc, ELF loader, kernel/QEMU/firmware | Artifact realizes reviewed sources | Hashes/tests only; executable correspondence open |

First proposed semantic connection: the bounded plan dispatcher and terminal
failure branch over the eight operation IDs, followed by the descriptor/seal
syscall interface. No existing C semantics proof is claimed. Trace tests and a
manual source map cannot discharge this ledger. Timing and hardware obligations
in [§FS-observations.hardware](../functional-spec/FS-observations.md#hardware-software-observable-channels) remain M5.

## audit: Evidence schema and replay gates

M2 records a strict schema, complete named profile, kernel/configuration/input
hashes, every initramfs file, tools/runtime/compiler identities, exact VM command,
positive controls, all ordered cases and raw serial transcript. Reject missing,
duplicate, malformed, stale or contradictory records. `--check-evidence` verifies
archived source/transcript structure; `--check-artifacts` additionally compares
available current native/kernel/image identities; an explicit VM run records a
fresh replay. Neither historical checking nor fresh tests certify C/Linux proofs.

Archived absolute command/environment/artifact paths belong to the recording
checkout. Derive that checkout from the exact emulator layout and check all
project paths against it, independently of the checkout running the validator.
Do not relax flags, guest identities or source hashes during this translation.
For `--check-artifacts`, map recorded project artifacts to the current checkout;
external compiler/runtime paths remain recorded host prerequisites. Regression
tests cover relocated archives, mixed roots and current artifact resolution.
