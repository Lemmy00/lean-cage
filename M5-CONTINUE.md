# M5 continuation: finish entry integration, then continue through all five deliveries

The user has assigned M5.1 through M5.5 in order and authorized integration and
push to `main` after each completed, validated delivery, with no permission step
between deliveries. The full acceptance criteria remain in
[§AR-application-verification](docs/architecture/AR-application-verification.md#ar-application-verification-prove-the-application-through-integrated-security-guarantees).
Do not reduce them to the partial results below.

**Status:** no M5 delivery is complete. M5.1 is in progress on
`milikic/proved-entry`, based on latest `main` at `69734d3`. The public product
continues using its accepted M4 implementation; `linux/workspace.c` and the root
build/image paths have not yet been switched to the new worker. Keep this partial
work isolated until its complete caller/source guarantee is integrated. M5.2–M5.5
have not started.

The runtime route was selected within the four-working-hour investigation bound:
start 2026-11-03 20:05 UTC, decision 21:58 UTC. See
[§DA-entry-worker](docs/decisions/architectural/DA-entry-worker.md#da-entry-worker-use-a-fresh-single-threaded-lean-entry-image).
Do not restart the runtime/general-importer investigation. The worker is a fresh
single-threaded Lean image; the native child executes it before Lean initialization.
The worker itself never forks. Task workers, libuv initialization and the extra
main thread are disabled explicitly; the worker also checks `Threads: 1`.

The current pieces are implementation work within M5.1:

- `launch/LeanCageEntry/Program.lean` and `Script.lean` define the actual setup,
  failure/preflight behavior and exec request. `Worker.lean` is the real parser
  and dispatcher; `Main.lean` rejects test modes and `TestMain.lean` enables them.
- `linux/entry_primitives.c` marshals the enumerated primitive effects.
  `linux/entry_handoff.h` is the candidate native handoff. It is used by the
  prototype's derived helper, not the canonical public build.
- `verification/launch/Admission.lean`, `StateProofs.lean`, `Effects.lean`,
  `Witnesses.lean` and `WorkerConnection.lean` check the shared body, physical
  authority projection under explicit primitive effects, failure prefixes,
  preflight, argument meanings and an inhabited non-restricted starting state.
  Credential operations permit collateral capability/dumpability changes;
  later explicit operations must reset them.
- `ArgumentConnection.v` and `ArgumentValues.v` strictly check the actual imported
  byte computation and the complete ordinary-Lean bound/value propositions.
  `NativeArguments.v` and `NativeValues.v` reuse the accepted numeric source
  semantics in the actual candidate helper and connect successful numeric reads
  to the worker decoder on the same owned bytes.
- `assurance/entry-{claims,arguments,native-values}` records exact types,
  transitive foundations and source identities. The compressed records retain
  their `.json.gz` suffixes. No source/caller completion is implied by these.
- `assurance/entry-route-vm.json` and its source/transcript/image archives bind
  the exercised caller-to-entry route. Normal native cases and the Lean API use
  production helper/worker images; injected cases use separate test images.
  The cohort has 11 native cases, check/run/report and six death/cancel boundaries.

**Exact next action:** extend the native source proof from the numeric call to
the complete `guest` handoff in the archived production helper. Prove the owned
stack objects, UID/descriptor formatting and read-back comparisons, alias checks,
argv table/terminator, mode/path binding and all error continuations. Produce the
same owned bytes consumed by `worker_parse_exact`; do not assume that connection.
The actual source AST is regenerated as `.tools/launch/source/EntrySource.v` by
`verification/launch/native.py`. Reuse `current_number_worker_value` and the
accepted numeric/memory certificates; keep all strict importer/kernel checks on.

Then prove the relevant `namespace_init` fork/stop/cgroup-attach/tracer/options/
resume prefix, with actual process identities, argument memory, errors, waiting
and loss. The `KernelTrace` premise in the body theorem is still an application
producer obligation. It cannot be inferred from raw success values: inherited
filters/tracers can forge them. The body-state projection also does not establish
the process-scope/resource projection or successful exec inheritance by itself.
Use [§AR-entry.work](docs/architecture/AR-entry.md#work-remaining-integration-within-the-entry-delivery) for the remaining entry acceptance map.

Prepared root/identity/policy producers are explicitly assigned to M5.3. Local
fork/handshake/argument binding stays in M5.1. Full supervision and truthful
cleanup/report provenance stay in M5.4/M5.5. No whole application component may
remain an unexplained trusted operation in the final composition.

Once the caller/source proof closes, integrate the worker into the single
maintained helper/build/image path, preserve/rebind historical proof evidence at
its actual scope, and run the complete affected acceptance. Only then mark M5.1
complete, integrate and push `main`, and proceed automatically to M5.2. The current
checks below validate partial work and do not replace that acceptance.

```sh
./scripts/check_entry.sh
python3 tests/entry/prototype.py --check-evidence
```

The first command includes the archived VM-record validation, strict source/value
connection and Lean declaration/axiom audit. It reuses unchanged foundation input
and proof identities. A fresh prototype VM is needed only after relevant runtime,
native, image, harness or input changes:

```sh
python3 tests/entry/prototype.py --record
```

For changed proof statements, `scripts/audit_entry.py --propose`,
`verification/launch/arguments.py --propose` and `verification/launch/native.py
--propose` write ignored proposals. Review changed types/definitions/foundations
before amending expectations. The public baseline's status-document amendment is
checked by `scripts/rebind_product_evidence.py`; it freezes original theorem,
axiom, native/Lean/Rocq source and checked-cache payloads. Never amend those hashes
merely to suppress a failure after a real implementation change.

The failed full-entry import, earlier runtime sources/probes and prior route
record are retained under `.tools/launch/`. The general import failed on the
pinned importer's old `UInt32` representation; the bounded byte interface works.
Hostile programs have run only in the designated disposable QEMU VM. No unrelated
project, global agent setting or shared host kernel was changed.
