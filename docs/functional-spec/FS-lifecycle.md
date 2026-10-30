# FS-lifecycle: M2 owned launcher lifecycle

This versioned M2 contract implements [§FS-launch.order](FS-launch.md#order-explicit-lifecycle) and [§FS-launch.lifetime](FS-launch.md#lifetime-descendants-and-teardown)
for `linux-x86_64-root-helper-m2-v1`. It preserves the M1 byte decoder and launch
contract unchanged. This is a static-native lifecycle profile, not M3 workspace
authority or an end-to-end Linux security claim.

## profile: Supported entry and privilege boundary

A trusted Lean controller validates the actual filter snapshot and emits one
fixed, versioned launch plan to a fresh, single-threaded native helper. The helper
is neither setuid nor an independently exposed privilege service. The operator
starts the controller as root inside the designated disposable VM. Reject other
kernel/marker/ABI profiles, non-root credentials, existing seccomp filters, external
tracing, unsupported plans and non-static executable images before guest entry.
Validate a fresh `/proc/self/status` descriptor with the actual PID, TracerPid 0
and Seccomp 0 as well as PR_GET_SECCOMP. An inherited filter can mask the prctl
query by returning errno zero; that alone is insufficient evidence of absence.
User namespaces are disabled in this profile; no unprivileged-helper fallback is
supported. The helper and namespace init are trusted and inaccessible to the guest.
Trusted root administration, the controller/helper images and Linux enforcement
remain environmental assumptions. Ordinary guest code need not cooperate.

## resources: Identity, ownership and bootstrap

Copy at most 16 MiB from an opened, no-follow regular executable into a private
memfd. Validate the copied ELF64 little-endian x86-64 ET_EXEC image, bounded program
headers and executable entry, reject PT_INTERP, seal write/grow/shrink/seal, then
execute that same handle with execveat(AT_EMPTY_PATH). Changing or renaming the
original after the snapshot cannot change the sealed image. Snapshot fidelity to
an operator's intended file while a trusted writer changes it is not claimed.
The fixed filter, argv, environment and plan are private copies in the helper.
Guest argv is `guest` plus one explicit bounded fixture argument; environment is
exactly `LC_ALL=C`, cwd is `/`, and umask is 077. No PATH or shell fallback.

Guest descriptors are exactly stdin from `/dev/null`, and public stdout/stderr
from the trusted VM console. Before exec, descriptors 3 and 4 temporarily own the
sealed executable and error pipe, both close-on-exec. Close every descriptor above
4, including inherited aliases, sockets, directories and control endpoints. No
guest descriptor carries supervisor/report/namespace authority. Parent and init
close only their owned endpoints; they do not close arbitrary caller descriptors.
Block signals before fork, reset all catchable dispositions (including reserved
Linux signals) in each fresh child, and unblock only after resetting. No inherited
Lean allocator/runtime or user handler executes in the native child.

## setup: Namespace and privilege order

Create owned PID, mount, IPC, network and UTS namespaces atomically with clone.
PID 1 makes mount propagation private and mounts procfs for its own PID namespace;
the root filesystem contents remain the VM's public fixture tree. M3 must replace
this with a workspace authority policy. No filesystem secrecy is claimed here.
Namespace init remains trusted root, sets dumpability to zero, and supervises the
untrusted child. The child clears supplementary groups, capability bounding and
ambient sets, sets real/effective/saved UID and GID to 65534, clears all effective,
permitted/inheritable capabilities, and validates the resulting credentials.
It then establishes no-new-privileges, installs the exact M1 filter, and immediately
executes the sealed static image. Unsupported operations, unexpected returns,
interruptions and ordinary setup errors are terminal. Restrictions need not roll
back on failure. New user namespaces and regaining root authority are unsupported.

## supervision: Stable ownership and typed results

The external helper owns namespace init through a pidfd and direct-child wait;
init owns the guest leader through direct-child wait/ptrace and all descendants
through the PID namespace. Numeric PIDs are never used after reaping to signal a
possibly reused process. Fork, exec, double fork, setsid and arbitrary guest steps
retain the namespace and installed restrictions under the stated OS contracts.
Use the trusted init's PTRACE_EVENT_EXEC observation to establish image replacement;
an empty error pipe alone establishes neither success nor absence of entry.
The trusted tracer does not modify guest registers or memory. It forwards guest
signals, observes exec, and does not expose a tracing interface to guest code.

Results distinguish guest exit (including exit 125), guest signal, setup failure
with operation/positive errno, completed cancellation, and unknown supervision.
A setup failure with a complete valid error frame certifies no guest entry. Lost,
short, malformed or failed reports yield unknown, retaining any observed entry.
Results carry separate guest-entry knowledge and namespace-cleanup evidence.
Protocol reads/writes handle short I/O and EINTR; setup calls are not retried.
Malformed/error reporting can never create a guest path.

Typed supervision decisions use the private report pipes. `M2_RESULT` console
lines are fixture diagnostics mixed with public guest output; console text and
the CLI exit code alone are not an authenticated result API. M3's reusable API
must keep guest output separate from its structured supervision result.

## cancellation: Requests, races and teardown

SIGINT, SIGTERM and SIGHUP to the helper request cancellation. A bounded native
fixture deadline is another cancellation trigger, not an M3 CPU/memory budget.
The helper sends SIGKILL through the owned namespace-init pidfd and waits for its
death. Only observed namespace-init death completes cancellation/namespace cleanup.
A racing exec may have occurred: cancellation reports unknown entry unless a
trusted exec observation was received. On normal leader exit, init kills all
remaining namespace members and reaps until ECHILD before reporting. On init death,
Linux tears down every process in that PID namespace, including session escapees.
No process outside the owned namespace is a cleanup target.

The helper and namespace init arm parent-death signals before permitting work and
check stable parent pidfds for the already-dead-parent race. The controller passes
its identity before spawning the helper; helper startup rejects adoption by a
different parent, including death before the first native parent lookup. The
guest relies on
namespace-init death killing its entire scope. Killing the controller/helper/init
must not leave the owned namespace running. Failure to signal/wait/report yields
unknown, never completed cancellation. Liveness requires fair scheduling, eventual
delivery of SIGKILL, terminating kernel calls and available supervision resources;
the safety proofs do not prove those OS premises or bounded wall-clock cleanup.

## model: Executable controller and effect contracts

The portable model has ordered operations, descriptor ownership, namespace and
credential records, entry knowledge, cancellation requests and live descendants.
Credential records use UInt32 for real/effective/saved/filesystem UID/GID, a list
of UInt32 supplementary groups, and UInt64 effective/permitted/inheritable/ambient/
bounding capability sets. Startup signals use two UInt64 masks and a UInt32
thread count. Before credentials/startup have been established their snapshots
are absent; guest steps may later change their own handlers without rewriting
the historical clean-startup snapshot.
The controller requests only the operation at the current program counter. A
successful effect updates actual modeled resources; errors are terminal for setup.
Guest fork/exec/exit and escape attempts are explicit adversarial transitions.
An escape attempt cannot change scope under the backend namespace contract.
Cancellation requests do not remove descendants or instantly stop a concurrently
running child; only observed scope destruction does. Logical birth identities
are never reused, whereas native numeric PIDs/fds may be recycled and require
pidfd/direct-child ownership. Cleanup can release only owned handles after scope
death. Include useful success/fork/exec
witnesses and failure/report/cancellation races. Prove reachable launch invariants,
descendant inheritance, terminal setup failure, owned-only cleanup, and an exact
projection of the successful filter segment to M1. These are conditional model
safety results; the manual native implementation map remains an M4 obligation.

The model records outside-signal attempts without modeling an external victim's
state. It proves descendant ownership/restriction inheritance, not the absence
of every external signal, IPC or filesystem effect. M3 must supply the authority
policy for those effects; the public VM fixture root is not a confinement policy.

## filter: General action of the preserved M1 program

Define an executable, fuel-bounded bytecode machine over the decoded instruction
table, unsigned UInt32 architecture/syscall words, accumulator, program counter,
loads, JEQ, JGE and RET. Unsupported instructions, invalid loads/targets or exhausted
fuel fail closed. Prove for all architecture/syscall words that the canonical nine
instructions kill on another architecture or syscall word at least 0x40000000,
return errno EPERM on native getppid (110), and allow other lower native words.
Connect decoder acceptance to this action. This is bytecode semantics, not a proof
of Linux's interpreter/JIT, and the filter still permits most native syscalls.

## observations: Public lifecycle disclosures

Plan/profile, input identities, operation/errno, guest stdout/stderr, exit/signal,
entry knowledge, cancellation and cleanup are public functional observations for
[§FS-observations.logical](FS-observations.md#logical-functional-observations). Timing, scheduling, resource use, caches, contention and
speculation remain [§FS-observations.hardware](FS-observations.md#hardware-software-observable-channels) obligations. No confidentiality or
workspace/network/resource-budget guarantee follows from this lifecycle slice.

## evidence: Acceptance and boundaries

M2 requires a separately named pinned capable kernel/configuration and initramfs,
positive namespace/socket/IPC/cgroup controls, allowed static workloads, all setup
boundaries and reporting failures, descriptor aliases, signals, existing filters,
fork/exec/daemon escape, parent death, cancellation and owned-only cleanup tests.
Record full theorem types/transitive axioms and exact source/artifact identities.
Bind both Lake packages' toolchain files and require the same pinned Lean version.
Archived evidence must remain checkable from another checkout: recorded absolute
paths describe the recording host, while source identities are repository-relative.
Require one consistent recorded project layout; never execute an archived command
to validate it. Comparing current artifacts resolves project-local paths within
the current checkout and requires the recorded external tools to be available.
Retain original M1 proofs and raw evidence. Historical evidence validation, current
artifact comparison and fresh replay are distinct operations. Native/compiler/
runtime/FFI, Linux, trusted administration and hardware gaps remain visible under
[§FS-assurance.assumptions](FS-assurance.md#assumptions-initial-assumption-and-obligation-register); no full confinement or production claim is authorized.
