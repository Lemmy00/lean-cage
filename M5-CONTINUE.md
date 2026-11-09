# M5 continuation: finish the host boundary, then continue through M5.5

The user assigned all five integrated deliveries, validated integration and push
to `main` after each, and explicitly rejected stopping at partial implementation.
Continue automatically. This file records state and does not authorize stopping.
The acceptance authority is [§AR-application-verification](docs/architecture/AR-application-verification.md#ar-application-verification-prove-the-application-through-integrated-security-guarantees) and the current delivery
is [§RM-roadmap.m5.next](docs/roadmap.md#m5next-current-assignment).

**Status, 2026-11-09:** M5.1 is complete. M5.2 is current; M5.3–M5.5 have not
started. Final entry acceptance is `assurance/entry-acceptance.json`. The public
bundle `77298fb97001ec611c9941962725c0e118046b35558b48d58b8b2352944ccda6`
passed all 12 CLI/library scenarios. Integration started from `69734d3`,
preserved earlier work at `be541b1`, and safely merged latest `main` `cf63751`
at `23e0d20`. The working M4 product and historical proofs retain their scopes.

## Completed entry guarantee

The maintained prepared-root launch statement establishes actual restricted
credentials, stdio/failure handles, filter, exact arguments and owned entry
scope before workload image replacement. Setup errors cannot fall through to
execution; preflight has a separate no-workload path. Actual source control and
the fresh Lean worker compose under the explicit Linux/runtime contracts.

- `verification/launch/process.py` owns the canonical C source graph, strict
  ordinary-Lean imports, full type/assumption/interface audit and independent
  kernel check. `assurance/entry-process.json.gz` records its checked artifacts.
- `NamespaceScopeFactory.actual_prepared_source_scope_from_raw` derives the
  source scope producer from actual preparation, fork, parent admission and
  private-channel source events. It assumes no local scope, admission,
  authorization, checkpoint, private invariant or whole-interval stability.
- Closed `ProcessEntryAcceptance.actual_entry_acceptance` retains one source
  tuple and its process, capability, queue, journal, IO, descriptor and source
  label history. `entry_runtime_ticks_ordinary` identifies its complete tick list
  with the exact worker/startup/image consumer. Full frame equalities additionally
  establish descriptor after maps; before-only ticks cannot establish them.
- `EntryGuarantee.production_source_workspace` consumes that producer at the
  actual release read. `CallerWitness.useful_public_source_workspace` derives
  native argument meanings internally from the same source-bound bytes, actual
  fork ancestry and complete worker execution. It supplies an inhabited useful
  restricted image and workspace task. Image replacement can still be at its
  exec stop; later supervision is M5.4.
- `assurance/entry-claims.json` binds executable bodies, full theorem types,
  transitive assumptions and source interfaces. The original body record remains
  preserved. Reviews are under `assurance/entry-*-review.json`.

The initial route investigation started 2026-11-03 20:05 UTC and selected the
fresh single-threaded worker at 21:58 UTC, within four working hours. See
[§DA-entry-worker](docs/decisions/architectural/DA-entry-worker.md#da-entry-worker-use-a-fresh-single-threaded-lean-entry-image). Native code executes a new Lean image before Lean initialization;
effectful Lean never resumes inherited runtime state after fork. Preserve the
bounded thread/runtime checks, strict narrow byte bridge, production/test-image
separation and failure/loss cases.

The final canonical audit caught and removed `Axioms.proof_irr` from clock-memory
loads without changing theorem types. It is partitioned without omitting queries,
and full independent kernel checking passed. Matching proof objects, exports,
ASTs, full types and foundations survived the final metadata-only amendments.
Do not replay them merely because of a handoff.

Earlier reporting evidence reads exact archived source inputs and sealed original
API/Main caches under an exact amendment/code guard. It is explicitly historical;
current source consumers and entry have separate records. See
`assurance/reporting-preservation-review.json`. Never substitute current cache
identities into the accepted old receipts.

## Current host work and exact next action

Finish [§AR-application-verification.host](docs/architecture/AR-application-verification.md#host-safe-host-boundary-for-arbitrary-vm-output): safe snapshots, per-run image/bundle
checks, bounded arbitrary VM framing, artifact validation, private publication
and retrieval, through CLI and reusable `Workspace`. Later deliveries supply
policy authority, owned lifetime and truthful inner observations. Keep those
producer obligations explicit; no whole application adapter may remain assumed
secure in the final M5.5 composition.

The read-only host map found these actual-source obligations: directory listing
materializes all names before its inode check; startup failure reads the entire
diagnostic before shortening it; run-zero artifact validation is incomplete;
export parsing can escape the transport error handler; retrieval does not recheck
aggregate policy bounds and follows ancestors. Diagnostic polling permits size
overshoot. Resolve them in the actual source-connected host path; a standalone
parser or plan is supporting work, not the delivery.

The isolated route prototype lives under ignored `.tools/host/prototype`. An
abi3 CPython C gateway calls a separate Lean image through `posix_spawn`, with
exact request/response bytes and bounded errors. The pinned Clight frontend
accepts the actual limited-API Python headers; gateway source and strict
ordinary-Lean interface compile. A real native `Workspace.run(bytes, UnicodePath)`
reaches the compiled Lean engine. Finish its checked accepted/error caller
connection, then record the route decision and host contract before moving it
into maintained code.

Prefer shared executable Lean control owning security effect sequencing. Python
must not remain an unchecked multi-operation plan interpreter. Account for the
small C gateway's CPython primitive marshaling, copied memory, actual ABI and
interpreter, GIL, signals, owned cancellation handles and spawn errors. Do not
embed an inherited Lean runtime or introduce an unassigned Python-verifier project.

The host needs a total bounded byte/JSON parser for arbitrary reports. The old
policy `StrictJson` is partial; its accepted-value bounds theorem does not prove
interpretation. Reuse the total parser for M5.3 after it serves the actual host
caller. Preserve policy versions, supported Unicode/escapes, useful executions
and failure/loss. Distinguish native raw-byte export names from the host's current
UTF-8 materialization restriction explicitly.

Freeze owned files/interfaces before parallel implementation. Keep maintained
modules responsibility-named. Run hostile workloads only in the designated VM.
Use focused checks, then the required affected gate once on final inputs; reuse
matching accepted evidence. Integrate and push each complete delivery to `main`,
then proceed automatically.

## Preserved subtleties for the remaining producers

- The entry cut is the actual allocated `State` at `namespace_tail 9`, not an
  uninhabited whole-`namespace_init` `Callstate`. M5.3 supplies its real prologue,
  root, identity, argv, object classification and ancestor producers.
- Retain actual fork incarnation/PID leases, descriptor aliases, widths, bytes,
  errors, arbitrary external steps and loss. A receipt label is not authority.
- Do not normalize `taskKey` by unrestricted computation: its multiplication can
  expand enormously. Rewrite the checked concrete actor keys first.
- An earlier rare cancellation failure remains under
  `.tools/launch/diagnostics/cancel-after-entry/failed`; retain it for M5.4.
  Later successful runs do not erase it or establish a lifetime proof.
- Detailed contracts and obligations are in [§AR-entry](docs/architecture/AR-entry.md#ar-entry-shared-executable-guest-admission-over-primitive-operations), [§FS-entry](docs/functional-spec/FS-entry.md#fs-entry-value-carrying-fail-closed-guest-admission),
  [§FS-assurance.entry](docs/functional-spec/FS-assurance.md#entry-entry-worker-body-and-route-evidence) and the reviewed claims. Compiler/runtime, precise Linux
  primitives, crypto identities and configured platform remain named assumptions.
  Kernel/hardware implementation research is the separate M6 track.
