# DA-entry-worker: Use a fresh single-threaded Lean entry image

**Status: route selected 2026-11-03 21:58 UTC; implementation/proof integration
in progress.** Investigation started at 20:05 UTC and resolved within the
four-working-hour bound in [§AR-application-verification.next](../../architecture/AR-application-verification.md#next-first-assignment-and-early-route-decision). Implement [§AR-entry](../../architecture/AR-entry.md#ar-entry-shared-executable-guest-admission-over-primitive-operations)
for [§FS-entry.runtime](../../functional-spec/FS-entry.md#runtime-dedicated-entry-runtime-profile) while preserving the delivered public product as the
acceptance baseline. This decision completes no M5 delivery.

## dependency: Thread and fork constraints

The pinned Lean toolchain reports commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc` (v4.35.0). Its generated main starts
the task manager and invokes `lean_run_main`; the runtime initializes libuv,
which starts an event-loop thread independently of the task manager. Setting
`LEAN_NUM_THREADS=0` is insufficient. The runtime also initializes signal state.
Do not move Lean computation into the forked child of an initialized Lean
controller. The existing single-threaded native helper avoids this problem.

Primary sources are the pinned upstream
[runtime initializer](https://github.com/leanprover/lean4/blob/v4.35.0/src/runtime/init_module.cpp),
[libuv initializer](https://github.com/leanprover/lean4/blob/v4.35.0/src/runtime/libuv.cpp),
[thread startup](https://github.com/leanprover/lean4/blob/v4.35.0/src/runtime/thread.cpp)
and [task manager](https://github.com/leanprover/lean4/blob/v4.35.0/src/runtime/object.cpp).
Record exact source/artifact identities with the executed prototype.

## worker: Fresh image with a bounded runtime surface

Use a fresh Lean worker image with task workers, event-loop initialization
and the extra main thread disabled explicitly at link/startup. It uses ordinary
Lean definitions over individually marshaled primitive operations, never forks,
and resets signal state after runtime initialization. All runtime operations
used after confinement must be available under the unchanged filter. Test the
actual helper-to-entry-to-workload path and setup failure in the disposable VM.

The worker links explicit wrappers for `initialize_libuv`,
`lean_init_task_manager`, `lean_run_main` and `pthread_create`; it also requires
`Threads: 1` in its bounded process-status snapshot. The native single-threaded
helper forks and immediately executes the fresh image. The worker itself never
forks, uses task/process/event-loop APIs or inherits initialized Lean state.
Pinned runtime/compiler correctness, synchronous allocation and the loader stay
explicit runtime premises. Startup failure, allocation failure and process loss
cannot supply a successful primitive reply.

The chosen route was exercised using the real `LeanCageM3.API` controller and
native namespace-init caller in a separate VM image. The source-frozen record
`assurance/entry-route-vm.json` binds the archived source recipe, image inventory,
worker artifacts and transcript. Its focused cohort covers useful shell/Python
entry, preflight, five setup-failure paths, lost/short failure records and
inherited handles, followed by check/run/report and six cancellation/death
boundaries. Normal calls execute the production worker. Only injected cases
select the separate test helper/worker, through an explicitly compiled test
handoff. Normal API calls use the production helper and worker; the production
helper disables test effects and rejects unsupported selectors before worker
entry. The maintained helper/build now uses this fresh image on the implementation
branch. Source/caller proofs and integrated acceptance are required before this
becomes a completed entry delivery on `main`.

## proof: Checked executable control and remaining source connection

The executing Lean control, concrete state/primitive contracts and finite-prefix
proof share definitions. `admission_at_exec` proves that an actual pending exec
requires the complete accepted setup trace; `admission_value_state` derives the
credential, handle-object, filter, root/cwd and argument values under individual
primitive contracts. Both are ordinary kernel-checked Lean results. Failure and
preflight prefixes exclude exec, including arbitrary returned error-write/exit
results. This is the body proof consumed by the remaining caller work.

The remaining native handoff, fork/stop/attach/resume and argument-memory binding
need source/caller proofs. The source must establish the trusted tracing and
unfiltered lineage: raw successful syscall returns alone are insufficient when
an inherited seccomp filter can synthesize results. Upstream prepared-root and
identity producers remain the explicit authority assignment; the local fork and
tracer handshake remain part of entry.

Keep the local fork/channel prefix in the narrow application function
`create_entry_child`. Its source proof covers socketpair, private duplication,
signal masking, fork, the child handoff and parent close in their existing order.
The actual `namespace_init` caller supplies its prepared descriptors and receives
the peer and child through owned cells before admission. This extraction bounds
the source-control proof without treating a multi-operation executor as trusted;
the preparation and later supervision interfaces keep their assigned scope.

Namespace init also captures the selected child PID, private peer, cgroup
descriptor and check mode into scalar locals before the first admission helper.
Their addresses are never exposed. The caller's source temporary environment
therefore retains the values through callbacks, and subsequent placement,
publication, release and supervision use those same values. This removes repeated
loads of mutable cells from the admission interface while preserving the owned
input behavior and operation/error order. The application still proves the
initial loads and every callback outcome; no complete native helper becomes a
runtime primitive.

The pinned strict bridge cannot import the entire new Lean closure: its older
predeclared `UInt32` representation conflicts with the pinned Lean representation.
Do not relax elimination/type checks or change the accepted importer. A bounded
byte computation interface imports with all checks enabled; its bound proposition
also has a kernel-checked Rocq proof over that exact imported executable decoder.
Use that small interface with the existing numeric/memory source evidence where
applicable. Neither the bounds proof nor the VM run proves native argument
binding. The native source and primitive-marshaling proof obligations must be
discharged before claiming the complete entry interface.

Reproduce route execution with `python3 tests/entry/prototype.py --record` and
validate the archived source-bound record read-only with
`python3 tests/entry/prototype.py --check-evidence`. Full application assurance
and the existing public product's claim manifest remain unchanged.

## release: Require an explicit private release byte after the tracing stop

To implement [§AR-entry.caller](../../architecture/AR-entry.md#caller-real-launch-interface-and-producer-map) and [§FS-entry.release](../../functional-spec/FS-entry.md#release-the-supervisor-explicitly-authorizes-continuation), a resumed
tracing stop is insufficient authorization. In pinned Linux 6.18.59,
`kernel/exit.c:forget_original_parent` calls `exit_ptrace` before
`find_child_reaper` invokes `zap_pid_ns_processes`. `exit_ptrace` queues SIGKILL
only if EXITKILL is installed, then detaches. `__ptrace_unlink` can wake a traced
child. A proof cannot silently treat namespace-init death as an atomic kill
before that detachment.

This is an ordering obligation found by source inspection, not a demonstrated
exploit in the configured VM. Its `CONFIG_SMP=n` and `CONFIG_PREEMPT_NONE=y`
would require additional analysis of voluntary scheduling to establish a race.
Instead of adding a global kernel-scheduling premise, use an application release:
the child reads exactly `0xA5` after STOP and before setup. The supervisor resumes
the stopped child only after placement and EXITKILL/TRACEEXEC installation,
checks that resume succeeded, then sends the byte. The resumed child blocks on
its private read until that check succeeds.
The existing four-handle ABI stays intact by replacing the private failure pipe
with a close-on-exec duplex socketpair. Failure records travel back in the
opposite direction. EOF, errors, unrelated bytes, loss and detachment without a
grant cannot reach workload exec.

The inspected tree is the bootstrap pin `1253a6aa5d104312bf0992afacc15220ae35bdf9`.
Its inspected SHA-256 identities are:

| File | SHA-256 |
|---|---|
| `kernel/exit.c` | `b67f8e165c15de57cab3a73a7479646ed45bafb64317d6d21697cefec0be7e74` |
| `kernel/ptrace.c` | `fb526a024bcc0d5b20e2dd42bc8424b6525ec50c3bbfeaf48976ffd0bff71f15` |
| `kernel/signal.c` | `034d2d03c820ca85e032877b0fbaf47b161c7ef34e4b9a9a036a5750fb321dc0` |
| `kernel/pid_namespace.c` | `74406bc27f3094e0b7723ff9694359cd4d04216563a80fc2ffd08a537353d26d` |

These sources justify the precise platform contract under review; they do not
constitute a kernel proof. All experiments remain confined to the designated VM.

## cgroup: Keep the writable attachment handle in the owning namespace

Implement [§FS-entry.release](../../functional-spec/FS-entry.md#release-the-supervisor-explicitly-authorizes-continuation)
under [§AR-entry.caller](../../architecture/AR-entry.md#caller-real-launch-interface-and-producer-map)
by opening the attachment handle in the clone child immediately before
`namespace_init`. Resource preparation creates and validates the cgroup before
the clone. The outer supervisor does not use the attachment descriptor; opening
it there created an unnecessary inherited writable alias. A child-only open
provides the local ownership boundary consumed by the fork/exec/close proofs.
Failure sends the existing stage-two setup result through the trusted init
channel and exits without creating the workload child. The public result and
argument interfaces remain compatible.

## prepared: Use the real prepared-root call site for the local entry contract

The input boundary of [§FS-entry.inputs](../../functional-spec/FS-entry.md#inputs-prepared-values-and-local-handle-validation)
is the existing prepared-root statement in `namespace_init`, immediately before
the guarded `create_entry_child` call, under
[§AR-entry.caller](../../architecture/AR-entry.md#caller-real-launch-interface-and-producer-map).
Its canonical allocated locals and owned argument memory are concrete inputs.
Source proofs establish the invariant at that actual statement and then execute
the complete local launch, including the common fork and both branches.

The filesystem prologue is the preparation producer assigned to
[§AR-application-verification.authority](../../architecture/AR-application-verification.md#authority-policy-authorized-workspace-construction).
Its native primitives are not yet executed by the local-launch semantics. A
whole-function source hypothesis therefore cannot witness this local result.
Use the inhabited prepared statement and keep the actual prologue/error-guard
producer explicit until that delivery proves it. This avoids both an opaque
`construct_root` success primitive and a behavior-preserving source refactor whose
only purpose would be moving the proof boundary. Local handle alias checks,
signal action, child identity, stop/placement/options, publication and grant
remain obligations of the entry delivery.
