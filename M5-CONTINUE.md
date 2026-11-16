# M5 continuation — M5.2 reduced to the host engine

M5.1 is complete and integrated. M5.2 is **partial implementation with checked
components**. The planning revision of 2026-11-15 in [§DA-host-delivery](docs/decisions/architectural/DA-host-delivery.md#da-host-delivery-deliver-the-host-boundary-in-two-parts-engine-first) reduces
M5.2 to the host engine guarantee. It assigns the gateway proof to M5.2b and
publisher authentication of stored results to M5.5. M5.3, M5.4, M5.2b and M5.5
remain assigned and incomplete. Finish M5.2 before advancing to those
deliveries. Its acceptance contract is [§AR-host-boundary.acceptance.engine](docs/architecture/AR-host-boundary.md#acceptanceengine-m52-closes-on-the-engine-guarantee-and-both-callers). The
complete host contract remains [§AR-application-verification.host](docs/architecture/AR-application-verification.md#host-safe-host-boundary-for-arbitrary-vm-output) and
[§FS-host-boundary.acceptance](docs/functional-spec/FS-host-boundary.md#acceptance-prove-and-consume-the-real-host-implementation); component checks are not delivery acceptance.

The existing public CLI/library and accepted entry guarantee remain the working
baseline. The native Python gateway and separate executable Lean host engine
are a candidate, reached through `leancage.native`; they have not replaced the
default public caller. No complete safe-host/public-result guarantee is claimed.

## What is preserved

The maintained implementation lives in `host/`, `linux/host_python.c`,
`linux/host_primitives.c`, the small Python build/alias modules and
`verification/host/`. It covers bounded request/response encoding, snapshots,
filesystem/VM effects, validation, staged authenticated publication and retrieval.
The architecture, behavior and route decisions are in [§AR-host-boundary](docs/architecture/AR-host-boundary.md#ar-host-boundary-execute-host-security-control-in-one-shared-lean-engine),
[§FS-host-boundary](docs/functional-spec/FS-host-boundary.md#fs-host-boundary-preserve-host-authority-and-bounds-for-arbitrary-vm-bytes) and [§DA-host-engine](docs/decisions/architectural/DA-host-engine.md#da-host-engine-use-a-small-native-python-gateway-and-a-separate-lean-host-image). See
[the integration review](docs/reviews/host-boundary-integration.md) for scoped
source connections and withdrawn historical assumptions.

The following records identify checked current components and their remaining
inputs, rather than independent completed deliveries. Under [§DA-host-delivery](docs/decisions/architectural/DA-host-delivery.md#da-host-delivery-deliver-the-host-boundary-in-two-parts-engine-first)
the root-handle, response-source, inherited-channel, file-copy and
cleanup-source records are inputs to M5.2. The parser, caller, initializer,
Outcome, channel-invocation, observation, callback and validation records are
inputs to M5.2b. The channel-source record divides: its engine source prefix
stays with M5.2, and its native reader and C receive producers go to M5.2b.

- `assurance/host-parser-source-review.json`: actual recursive C parser, all
  supported numeric/container branches, alias-aware aggregate ownership and
  original caller buffer permissions, with full statement/axiom review.
- `assurance/host-caller-checkpoint.json`: the actual call72 consumer reaches
  decoded graph and real EOF; owned-close, reap and restore components retain
  their individual contracts. It does not yet compose the entire public return.
- `assurance/host-response-source-review.json`: actual same-journal pending writer
  provenance before any current write acknowledgement or future engine return.
  The stream writer additionally derives response identity and writer offsets.
- `assurance/host-root-handle-checkpoint.json`: actual creation/reopen/stage
  receipts connect to the same recorded root lifetime and current handle.
- `assurance/host-initializer-objects-review.json`: actual import/class setup,
  pointer-store, failure and reentry rejection source; individual SDK reference
  laws have no assumed whole-initializer or callback-global frame.
- `assurance/host-outcome-reference-checkpoint.json`: checked Outcome
  allocation/store/return and reference-adoption support; original public caller
  composition is still required.
- `assurance/host-channel-invocations-review.json`: actual fresh exchange
  allocations and same-call socketpair rows supply shared invocation/pair data.
  The strict append preserves every previous native-data declaration.
- `assurance/host-observation-allocation-repair.json` and
  `assurance/host-observation-source-amendment.json`: the real getter now
  propagates allocation/lookup errors; exact non-getter definitions are retained.
- `assurance/host-inherited-channel-review.json`: the actual directory-close ABI
  checks its retained descriptor against `dirfd` before closing. The source
  borrowing proof supplies inherited channel references through nested scans;
  the native owned-directory mismatch/matching-close fixture passes.
- `assurance/host-file-copy-offset-amendment.json`: regular-file copies select
  their own checked offsets through the existing read ABI. The real owned-file
  fixture retains all 131273 bytes across four cursor changes. The source proof
  connects bounded open/read/close and the actual parsed manifest to initial
  installed bytes under exact per-read identity, content and no-modification
  interval observations. Their cumulative source/history producer remains open.

The resumed callback source lane now derives private-address origin retention
and the conditional five class/flag cell frame from finite nested registered
source callbacks. `GatewayCallbackRetention` consumes actual source control,
individual memory origins and the interpreter queries' ABI return shapes.
`GatewayLinkedAddresses` preserves the original source global addresses under
genuine SDK linkage. `GatewayRuntimeRetention` and `GatewayCallerClassCells`
produce current class-cell loads for their actual SDK/caller prefix consumers.
`assurance/host-callback-source-review.json` now records the full declaration,
primitive interface and assumption review against the zero-exclusion replay of
1269 frozen sources. Its evidence archive preserves the independent kernel
check and actual GC fixture. Review found and corrected the earlier omission of
the dynamically passed native signal handler from callback admission; the
predecessor remains preserved. The cumulative initializer class-root/reference
composition is still required. The actual native
GC fixture releases 64 owned manual Outcome cycles and preserves later use;
`GatewayGCVisitorSource` constructs the maintained traverse body's source path
to the genuine nonempty SDK visitor binding.

The resumed result-validation lane now starts at the original Outcome call.
`GatewayValidationEntry.gateway_actual_validation_entry` derives its four actual
native output slots, their permissions and separation from retained source
regions. `GatewayValidationNames` derives the relocated fourteen-name table,
ASCII/UTF-8 names and JSON-name bytes from the same retained loader regions.
`GatewayValidationTypeChecks.gateway_actual_validation_type_check` follows the
actual required and optional helper calls, including optional None. Its observed
comparison proof needs no stronger pointer-validity assumption. A positive check
retains the same received graph, source credits and caller-cell snapshot; SDK
exception returns are not assumed to preserve normal readiness.
`GatewayValidationFailureJoin` composes actual missing field/JSON lookups with
the real NULL type-helper and rejection returns. `GatewayDictionaryIteration`
accounts separately for borrowed results and each of the three native output
stores. These are checked integration components; the cumulative validation-loop
to private-copy/Path/owned-result return is still unfinished.
`assurance/host-validation-source-review.json` and its evidence record preserve
the complete 114 declaration types/assumptions, eleven interface bodies and
independent kernel check against the 1295-source complete replay.

`assurance/host-channel-source-review.json` records the source read taxonomy,
object-and-OFD raw-engine exclusion and source-conditioned physical prefix
consumer. Its outstanding actual recording, SDK/child/foreign reader and C
receive producers remain explicit. `assurance/host-cleanup-source-review.json`
records actual universal unlink dispatch, creation and in-progress stage
reference consumers; the complete custody fold and installation intervals
remain open.

Detailed ownership and response obligations remain in
`assurance/host-ownership-status.json` and
`assurance/host-response-obligations.json`. Other component records retain their
original scope. The final checkpoint validation inventory belongs in
`assurance/host-checkpoint.json`.

## Remaining M5.2 work on the host engine

Work in this order. [§RM-roadmap.m5.next](docs/roadmap.md#m5next-current-assignment) carries the same list and the effort
limits.

1. **Final statement and closing statements: done on 2026-11-15.**
   `verification/host/EngineGuarantee.lean` states `EngineGuarantee.Statement`
   over the existing journal types with the premises of
   [§DA-host-delivery.engine](docs/decisions/architectural/DA-host-delivery.md#engine-what-m52-proves-and-which-premises-it-names), and kernel-checks `statement_of_closings`: the
   statement follows from `FoldClosing`, `InstallationClosing` and
   `ResponseClosing` with the existing source and journal theorems. The fold's
   per-tick inputs are `EngineStepClosing` and `ExternalStepClosing`; the model
   statement is `ModelClosing`. No closing statement is proved yet.
   `assurance/host-ownership-status.json` records the declarations and the
   findings below.
2. **Build the model.** Prove `ModelClosing`: one concrete filesystem,
   process and channel model inhabits `Platform`, `Operator` and `Premises`,
   with a useful complete request whose response channel satisfies
   `ResponseWitness`, a rejected request and a lost-reply execution. No such
   instance exists yet. The present witness modules cover only the pure
   transport, snapshot, artifact, publication and VM-read components.
3. **Finish custody for individual operations.** Prove `EngineStepClosing` and
   `ExternalStepClosing`. Every Entrypoint unlink, mkdir and exclusive file open
   already advances the same registered publication state; these steps must
   also certify `OwnedTick`. Complete ordinary opens and allocation, the other
   engine effects, and the namespace effects of the validator and VM child
   processes. Derive the engine's anchor operands in this step; the children's
   anchor operands are now the `Children` premise.
4. **Prove the whole-execution theorem.** Prove `FoldClosing` by induction
   over the recording from `initial_registered_publication` and the two
   per-tick closing statements. Prove `InstallationClosing` from it and the
   operator premise, and `ResponseClosing` from custody and
   `ExclusiveLaunches`. `statement_of_closings` then gives the final theorem.
5. **Switch the callers.** Repair the signal-target defect recorded in
   `assurance/host-signal-target-obligation.json` in the gateway source, with a
   regression test. Its proof stays with M5.4. Make the public CLI and
   `Workspace` use the engine by default, and remove the earlier Python
   snapshot, decoder and publisher from the public path.
6. **Accept.** Run the acceptance of [§AR-host-boundary.acceptance.engine](docs/architecture/AR-host-boundary.md#acceptanceengine-m52-closes-on-the-engine-guarantee-and-both-callers) on the
   identified bundle in the disposable VM. Record the engine claim, its
   premises and the gateway as a tested, unproved native adapter.

No reliable completion-time estimate follows from the number of checked
components. Progress is the number of closing statements proved. The stop rule
is in [§RM-roadmap.m5.next](docs/roadmap.md#m5next-current-assignment). Final M5.2 acceptance has not passed or been claimed.

## Where each open item goes

| Open item and record | Delivery |
|---|---|
| `global-source-family-fold`, `same-birth-directory-custody`, `public-path-and-cwd-custody`, `foreign-and-backend-interference` in `assurance/host-ownership-status.json` | M5.2, steps 3 and 4. Their fixed-key and exposure consumers go to M5.5 |
| `joint-usefulness-and-acceptance` in the same record | M5.2, steps 2 and 6, for the engine contracts |
| `native-handoff-coupling`, `native-callback-operation-coverage` in the same record | Named premises of M5.2; produced by M5.2b |
| `key-and-marker-observation-origin` in the same record | M5.5. M5.2 proves only that retrieval performs its checks |
| The four `remaining` entries of `assurance/host-response-obligations.json`: engine writer to native reads, `host_outcome_from` validation and copies, observation and getter dispatch, initialized class and reference authority | M5.2b, except the engine half of the first entry. That half stays in M5.2 as `ResponseClosing`: the checked writer-prefix theorem takes its write sources as a hypothesis, so only its conclusion is checked |
| Conversion from the contradictory root-lease contract in `assurance/host-reference-ownership-amendment.json` | M5.2b |
| `assurance/host-runtime-activation-obligation.json`, `assurance/host-descriptor-origin-obligation.json` | M5.2b |
| `assurance/host-signal-target-obligation.json` | Source repair in M5.2 step 5; proof in M5.4 |

`assurance/host-ownership-status.json` now records the closing statements.
The response record keeps its wording; this table assigns its entries.

### Step 1 findings

- The final statement fits the existing journal types. Its custody conclusion
  uses `RegisteredCustodyExecution` along the actual `NativeExternalJournal`;
  the per-tick closings use `RegisteredPublicationState` and
  `JointPublicationPrefix`, bound to the recording's own selected rows.
- The engine also creates missing public ancestors of the output path, so the
  owned-effects conclusion allows fresh, nonreplacing bindings in public
  directories. It allows no change inside another request's private scope.
  The acceptance text is corrected accordingly.
- The response writer's engine half was not complete: proving
  `ResponseClosing` needs a premise that no other engine actor inherits the
  same endpoints. It is `ExclusiveLaunches`, part of the engine-start premise
  that M5.2b must produce.
- The contents conclusion still permits a write on an unnamed, unlabelled
  object, which covers the response and VM-control sockets. Excluding unnamed
  files would need a socket-versus-file distinction or the descriptor's origin
  in the world model.
- The response conclusion quantifies over every channel history of the run.
  `ResponseWitness` in `ModelClosing` makes the model show it is not vacuous.

## Exact restart point

Start with step 2 above, `ModelClosing`. The checked interfaces to reuse for M5.2 are
`CallerProofs.actual_application_complete` for the functional result,
`FilesystemCommitGuarantee.actual_authenticated_commit` for the selected commit,
the joint unlink, mkdir and exclusive-open modules for individual operations,
and `GatewayFraming.actual_response_prefix` for the response writer. Do not
reopen their unchanged proofs. The proof step recorded before the revision is
ordinary open/allocation and child namespace dispatch, followed by the
cumulative same-journal custody execution.

For M5.2b, `GatewayReferenceParserComplete.gateway_reference_actual_parser_complete`
and `GatewayResponseDecoded.actual_exchange_decodes_response` are the checked
parser/consumer interfaces to reuse. Do not reopen their unchanged numeric
proofs. That delivery starts with its final statement, the conversion from the
contradictory root-lease contract and one model of the CPython and libc
contract records.

Historical unfinished proofs are preserved as non-acceptance text drafts in
`verification/host/drafts/`. The framing draft has been superseded by the checked
maintained prefix proofs and `assurance/host-framing-review.json`; do not restart
its failed preparation. Cleanup status retention still needs its actual caller
join. The historical drafts remain excluded from maintained source discovery.

The M5.4 signal-target issue is independently recorded in
`assurance/host-signal-target-obligation.json`: automatic child reaping can permit
raw process-group ID reuse. Repair the actual implementation before claiming
owned cancellation; a successful raw signal operation is not a lifetime proof.

`assurance/host-runtime-activation-obligation.json` records the exact runtime
instantiation boundary: `gateway_spawn_ambient` and held-thread resource frames
apply only when the same physical activation survives. An SDK/callback exec or
exit must enter committed-loss/dead control, preserving the actual retirement
history; it cannot resume old C control with a descriptor frame. The scoped
activation adapter still needs its actual episode/public-caller instantiation.
`assurance/host-descriptor-origin-obligation.json` separately records the older
descriptor-origin interface's missing existing-inode/fresh-OFD case. It requires
a corrected origin or a proved source-domain restriction before instantiation;
it is not an unconditional Linux law for `O_PATH` socket-inode aliases.

## Validation and evidence reuse

The checkpoint preserves focused Lean/Rocq kernel/type/axiom checks and their
source identities. Earlier runtime/VM evidence keeps its own identified inputs;
it is not final M5.2 acceptance. Hostile workloads remain confined to the
recorded disposable VM.

Five C comment edits fixed citation width and removed an unjustified PID-ownership
comment. `assurance/host-source-comment-amendment.json` preserves the exact old C
and generated program and records their identical Clight bytes. The later
observation-getter repair has an explicit behavior amendment and new Clight
identity `db117a9df6130d16`. Its source-retention proof and combined replay retain
the unaffected callers. Historical component bindings remain at their original
epochs; the next aggregate delivery record must consume each amendment.
The Outcome required-field repair adds the explicit
`assurance/host-outcome-source-amendment.json`. Its zero-exclusion replay checks
all 1192 sources present at that frozen input set, including the earlier pointer
and reference-token leaves. New callback/source composition remains active work
after that set. The original typed-framing statements, proof bodies, interfaces
and assumptions remain exact; their explicit source metadata amendment binds
the current compiled objects.

The subsequent independent check exposed a shared-cache name collision: an
ignored draft overwrote a maintained module's compiled object. The maintained
source and its reverse clients were restored and independently checked. Drafts
now use distinct module names. `verification/host/source_replay.py` records failed
aggregate/checker diagnostics and checks the maintained inventory, copied source
and object identities before accepting a replay. The corrected frozen replay at
`source-replay-20261110T173710725222Z` passes with no exclusions or detected drift;
the callback evidence archive preserves its result and inputs. This repair and
supporting evidence do not constitute M5.2 acceptance.

The final checkpoint manifest records the foundation/product check, the affected
host build, matching source/object inventory, ordinary/Rocq query evidence,
native compile and Git integration. These checks preserve a reviewable partial
checkpoint; they cannot establish the four unfinished guarantees above.

The checkpoint's current public-product gate passed. Because the two optional
Python modules changed its source inventory, the existing disposable workspace
VM was actually replayed: 67 cases, three API checks and six death/cancellation
boundaries passed. The previous exact records are preserved in
`assurance/host-workspace-checkpoint-before.json.gz`; only the reviewed input
fingerprints of the workspace theorem record changed, with every theorem,
assumption, predecessor and scope field preserved. This is baseline product
validation, not final host-candidate acceptance.

On 2026-11-15 the modules for preparing and exclusive-open custody, descriptor
origins, presentation and validation passed the integrated
`lake build HostVerification` (651 jobs) and the incremental source replay
`source-replay-20261115T015222128095Z`: 1339 sources, no exclusions or drift,
aggregate and independent kernel check. This is component validation, not
delivery acceptance.
