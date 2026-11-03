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
helper excludes the environment-based selector assignment as well.
This is route evidence; the maintained public bundle still uses the accepted
baseline until the source/caller proofs and integrated gate are complete.

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
