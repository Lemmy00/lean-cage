# M5 continuation — user-requested M5.2 pause

M5.1 is complete and integrated. M5.2 is **partial implementation with checked
components**, paused at the user's explicit request. M5.3, M5.4 and M5.5 remain
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
   until excluded. Prove canonical typed framing/prefix uniqueness so that the
   actual writer value and actual parser value agree; broad `SourceEncoded`
   alone intentionally permits scalar tags that cannot supply this conclusion.
2. **Finish initialization, public extraction and Outcome ownership.** Compose
   the actual SDK callback source/global-write authority, current regions and
   reference histories. Join Outcome allocation with copy-credit adoption at
   the actual older stack, derive the data-cell/result bindings, and compose the
   real 14-field/dictionary-copy/Path/observation callers and getters. Do not
   assume stable callback-writable globals or an empty retry state.
3. **Close filesystem custody and authenticated publication.** First construct
   the selected commit consumer from `PrimitiveCommitResources`,
   `primitive_created_stage_continuation`, `opened_root`, `shared_handles`,
   `current_reference` and `source_nondestructive`. Then fold the whole actual
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

Two unfinished proofs are preserved as explicitly non-acceptance text drafts in
`verification/host/drafts/`: canonical framing preparation and cleanup status
retention. They are excluded from maintained Rocq source discovery, and no
security result consumes them. Each draft has its exact next action and failure
record. All maintained source modules at this checkpoint have checked objects.

The M5.4 signal-target issue is independently recorded in
`assurance/host-signal-target-obligation.json`: automatic child reaping can permit
raw process-group ID reuse. Repair the actual implementation before claiming
owned cancellation; a successful raw signal operation is not a lifetime proof.

## Validation and evidence reuse

The checkpoint preserves focused Lean/Rocq kernel/type/axiom checks and their
source identities. Earlier runtime/VM evidence keeps its own identified inputs;
it is not final M5.2 acceptance. Hostile workloads remain confined to the
recorded disposable VM.

Five C comment edits fix citation width and remove an unjustified PID-ownership
comment. `assurance/host-source-comment-amendment.json` preserves the exact old C
and generated program and records that the pinned frontend produces **identical
Clight bytes** from the current C. Historical component source bindings are not
silently refreshed. The next aggregate delivery record must consume that
amendment explicitly.

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
