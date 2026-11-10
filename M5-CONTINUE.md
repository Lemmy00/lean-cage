# M5 continuation — resumed M5.2 implementation

M5.1 is complete and integrated. M5.2 is **partial implementation with checked
components**, resumed at the user's explicit request after the committed pause.
M5.3, M5.4 and M5.5 remain
assigned and incomplete. Resume M5.2 before advancing to those deliveries.
The acceptance contract remains [§AR-application-verification.host](docs/architecture/AR-application-verification.md#host-safe-host-boundary-for-arbitrary-vm-output) and
[§FS-host-boundary.acceptance](docs/functional-spec/FS-host-boundary.md#acceptance-prove-and-consume-the-real-host-implementation); component checks are not delivery acceptance.

The existing public CLI/library and accepted entry guarantee remain the working
baseline. The new native Python gateway and separate executable Lean host engine
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
inputs, rather than independent completed deliveries:

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

## Remaining completion work

1. **Connect the physical response to the same caller and decoded value.** Join
   the actual pair birth, source leases, per-operation IPC/OFD lifetime/custody,
   monotone partial writes and caller receives. Derive exclusive read/discard
   authority from the actual source history, retaining other-reader/discard cases
   until excluded. Canonical typed framing/prefix uniqueness is now checked in
   `GatewayFraming` and `GatewayResponseFraming`; the actual writer view and parser
   heap supply the tag restriction. `GatewayDecodedFraming` consumes the real
   call72 parse result while preserving its source ticket, graph and descriptor.
   Supply its actual common-byte-prefix input from the physical channel history;
   broad `SourceEncoded` alone intentionally permits ambiguous scalar tags.
2. **Finish initialization, public extraction and Outcome ownership.** Consume
   the derived SDK callback source/global-write authority in the cumulative
   current regions and reference histories. Join Outcome allocation with copy-credit adoption at
   the actual older stack, derive the data-cell/result bindings, and compose the
   real 14-field/dictionary-copy/Path/observation callers and getters. Do not
   assume stable callback-writable globals or an empty retry state.
3. **Close filesystem custody and authenticated publication.** The selected
   `FilesystemCommitGuarantee.actual_authenticated_commit` consumer now joins
   those actual source/current-root/custody inputs. Complete the whole actual
   global custody/commit/key-origin history, including aliases, uncertain commit,
   cancellation, hostile output, failed operations and lost acknowledgements.
4. **Compose and accept the delivered host guarantee.** Join original argument
   extraction, request/header/stream/ledger producers, EOF, closes,
   Save/Reap/Restore, status/result/stack-free and Outcome projection on the same
   run, with all error/loss cases. Integrate both documented public callers only
   after the proof connections hold. Run the required final identified bundle
   acceptance, including the affected hostile VM/snapshot/export/storage cases.

These are substantial end-to-end proof/integration obligations. No reliable
percentage or completion-time estimate follows from the number of checked
components. Final M5.2 acceptance has not passed or been claimed.

## Exact restart point

Start with the physical channel/canonical framing connection and selected-commit
current root consumer above, while the Outcome/initializer lane composes its
actual caller. `GatewayReferenceParserComplete.gateway_reference_actual_parser_complete`
and `GatewayResponseDecoded.actual_exchange_decodes_response` are the checked
parser/consumer interfaces to reuse. Do not reopen their unchanged numeric proofs.

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
