# FS-entry: Value-carrying, fail-closed guest admission

Refine [§FS-linux-product.proofs.entry](FS-linux-product.md#proofsentry-establish-actual-state-at-workload-entry) for the maintained offline workspace.
This contract is an implementation target. Delivery includes the caller and
adapter proofs, not only a standalone setup model.

## inputs: Prepared values and local handle validation

Admission receives the leased 32-bit UID/GID, prepared root object/path, owned
namespaces and resource scope, the bounded workload argv, and four owned handle
slots. The stdin, stdout, stderr and failure slots must be distinct, at least
four, and fit a signed 32-bit descriptor. Their objects are respectively the
frozen input, capture writers and private release/failure socket endpoint. Preparation owns
their classification; admission checks the numeric alias restrictions itself.
Argument strings are nonempty, NUL-free UTF-8 within the existing policy bounds.
The first executable remains `/bin/sh` or `/usr/local/bin/python3`.

The private worker handoff carries mode, UID, root, the four descriptor numbers,
the selected test mode and workload argv. Numeric fields use canonical ASCII
decimals: no sign, whitespace, leading zeroes, overflow or narrowing loss.
This internal ABI does not replace the public policy format. The production
native handoff and entry executable both reject non-normal selectors. Fault
injection uses a separate test executable and an explicit native test build.
For normal inputs the two Lean entry builds execute the same definition.

## control: Primitive sequencing and failure

The executing definition must issue concrete operations and inspect their actual
returns. A failed or unexpected setup return cannot reach any later setup
operation or workload exec. Reporting failure, partial writes, asynchronous death
and loss cannot reopen setup. Safety holds for finite execution prefixes;
termination requires primitive progress and scheduling assumptions separately.

Validate PID-valued and mode-valued returns against their actual ranges; neither
zero from a PID-returning operation nor an out-of-range mode is successful setup.

The allowed entry has the requested root and `/workspace` cwd; standard handles
refer to the supplied objects; only the private close-on-exec failure writer may
remain before exec. Signal dispositions/mask, IDs, groups, capability sets,
securebits, dumpability, no-new-privileges and exact filter satisfy
[§FS-linux-product.proofs.entry](FS-linux-product.md#proofsentry-establish-actual-state-at-workload-entry). The workload argv and fixed environment are the
values supplied to the successful image-replacement operation.

## release: The supervisor explicitly authorizes continuation

Open the writable run-cgroup attachment handle only in the namespace-init
process, after its outer clone and before local child creation. The outer
supervisor keeps no inherited writable alias of this handle. A failed open
reports a stage-two setup failure and terminates that init without creating a
workload child. Preparation binds the opened handle to the owned cgroup object;
local fork/exec/close proofs account for its subsequent aliases.

After its tracing stop, the worker must read exactly the private supervisor's
release byte (`0xA5`) before restricting handles or proceeding with setup. The
supervisor may send it only after placing this stopped child in its owned cgroup
and installing the required tracing options, then observing successful resume.
The caller must also observe successful cgroup-descriptor close and required
admission-frame publication before invoking that resume/grant sequence. A zero
clock measurement denotes an unavailable or rejected measurement and latches
setup failure before publication or release. A later receiver's rejection cannot
repair an earlier release of the child.
The supervisor captures the selected child, private peer, cgroup descriptor and
check/run mode before calling admission helpers. The same captured values select
placement, descriptor close, release and later child observations; helper memory
writes cannot change which process or channel those actions target.
The resumed worker blocks on the release read until that final check succeeds.
A stop's return, tracer detachment,
EOF, short read or unrelated byte cannot authorize continuation. The private
channel is a duplex socket: its child endpoint also carries the existing eight
failure bytes in the opposite direction. Fresh worker exec closes the inherited
parent endpoint; no workload or other run can supply a release byte.
The matching socketpair operation creates empty queues for that object instance.
The release proof retains the same object and physical operation sequence from
creation through the accepted read; reusing an observation's numeric label
cannot preserve bytes belonging to an earlier object.

## check: Preflight never executes a workload

Preflight exercises the same supported setup restrictions without a workload
exec. Its trusted success record is distinct from observed workload entry. Both
preflight and run fail closed; a lost record remains unknown at the receiver.

## image: Preserve authority across successful image replacement

The entry guarantee includes the successful workload `execve`, rather than
ending at the call. Image replacement preserves the restricted root, cwd,
namespace/resource membership, no-new-privileges and installed filter. It closes
every close-on-exec descriptor, so the private failure writer cannot reach the
workload. The three standard descriptors retain their supplied object identities.
The workload receives the exact argument and environment bytes checked at the
call; a returning or lost exec cannot produce an entry observation.

Linux resets saved IDs to the effective IDs during exec. Since setup establishes
all four ID slots to the leased identity, that reset preserves the required
identity. With empty capability sets, the empty bounding set, locked securebits
and no-new-privileges, exec cannot acquire capabilities. Linux clears the
keep-capabilities bit; the required securebits do not set it. Dumpability is
checked as zero before exec, but Linux chooses its post-exec value from executable
metadata and kernel settings. The post-exec authority claim does not assert a
zero dumpability value. The actual exec-time tracer context must also preserve
active filter enforcement. A safe earlier filter-install return does not justify
inheritance after an intervening tracer-option change.

## provenance: A return value does not prove the requested effect occurred

An inherited seccomp filter can synthesize a successful return without executing
the requested operation. Model that execution as well as genuine kernel returns.
Do not infer credential changes, filter installation or absence of inherited
filters from a raw success status without establishing its provenance. The real
caller must supply the supported clean process lineage, ownership and observation
producers. A body theorem conditional on those producers is not the complete
entry guarantee in [§FS-linux-product.proofs.entry](FS-linux-product.md#proofsentry-establish-actual-state-at-workload-entry).

The filter projection describes active kernel programs. A tracer can suspend
seccomp enforcement without falsifying a successful install return. Establish
the actual SETOPTIONS payload and its ownership, including the absence of
`PTRACE_O_SUSPEND_SECCOMP`, as well as the allowed request opcodes. Check the
physical tracer context again at successful workload replacement. Foreign,
intercepted and suspended executions remain in the broad runtime relations;
only the source-connected protected caller can supply the entry guarantee.

The supervising parent must establish default `SIGCHLD` handling with no
automatic-reap flag at the local fork boundary and retain exclusive wait
ownership until admission completes. A stopped-child observation alone cannot
justify continued PID ownership when automatic reaping is enabled. Setup must
fail before fork if this local signal-action setup fails.

## runtime: Dedicated entry runtime profile

No Lean runtime state may be inherited across a fork into effectful Lean code.
A fresh entry image may use the pinned runtime only with an explicitly identified
startup profile that creates no additional thread. It cannot call task, process
or event-loop APIs. Reset signal state after initialization. Bound argument and
filter memory before confinement, retain it through the corresponding syscall,
and account for allocation failure and unexpected runtime termination as loss.
Runtime/compiler behavior stays in [§FS-linux-product.trust](FS-linux-product.md#trust-platform-assumptions-for-the-initial-product); a runtime
configuration is never evidence for an application control theorem.
