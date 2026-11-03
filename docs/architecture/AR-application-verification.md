# AR-application-verification: Prove the application through integrated security guarantees

Implement [§FS-linux-product.proofs.application](../functional-spec/FS-linux-product.md#proofsapplication-the-complete-application-guarantee) on the delivered public workflow.
This is the M5 implementation plan; all deliveries below are planned. The
baseline is `92367a5`, with accepted evidence in the
[product handoff](../reviews/workspace-product-handoff.md). The roadmap owns
sequencing under [§RM-roadmap.m5](../roadmap.md#m5-verify-the-complete-application-control-path); this document owns proof boundaries, code
coverage and acceptance. Keep the existing policy, result and VM interfaces.

## boundary: Include the complete per-request application

| Component | Application work to prove | Reusable evidence |
|---|---|---|
| `python/leancage/runner.py`, `protocol.py`, `snapshots.py`, `cli.py` | Request validation and binding, safe snapshots, VM ownership, channel interpretation, bounded publication/retrieval | Product contracts and acceptance tests; the host invokes the shipped Lean policy validator |
| `linux/vm_init.c` | Request handoff, controller invocation, helper identification/cancellation, private result/artifact transport and inner-scope observations | Existing implementation and VM scenarios |
| `workspace/Main.lean`, `workspace/LeanCageM3/API.lean`, `library/LeanCageWorkspace.lean` | Executable policy-to-argument construction, process/pipe ownership, result observation and publication | Policy/filter/decoder proofs and exact public-definition bindings |
| `linux/workspace.c`, `linux/artifacts.h` and shared headers | Native setup, admission, supervision, resource accounting, capture/export and reporting | Accepted input/parent contracts and conditional source/compiler reporting proofs |

Build preparation and installation are trusted operator/bootstrap inputs to this
profile. M5 must still prove the per-request checks and use of the identified
bundle. The shipped `build.py` helpers used during request execution belong to
the application coverage map, even though release build reproducibility belongs
to [§RM-roadmap.m7](../roadmap.md#m7-supported-releases-and-maintenance). Explicitly account for every helper reachable from the public
path; a language boundary cannot silently add a trusted application component.

Linux, compiler/libc/Lean runtime, host Python runtime, QEMU and hardware retain
the precise trust permitted by [§FS-linux-product.trust](../functional-spec/FS-linux-product.md#trust-platform-assumptions-for-the-initial-product). Hash-based identities
also require their stated cryptographic assumptions. Application source proofs
establish behavior under those contracts; hashes bind evidence to artifacts.
Neither a source hash nor a test establishes source correspondence.

## method: Choose a proof route that reaches the real caller

Prefer executable decision/control definitions in ordinary Lean over primitive
effects, shared by execution and proof. This follows [§DA-lean-linux](../decisions/architectural/DA-lean-linux.md#da-lean-linux-build-a-lean-replacement-with-linux-as-the-first-backend) and avoids
maintaining a hand-translated model beside the real control path. Extend primitive
effects only as needed by the assigned guarantee. Every effect has concrete
arguments, memory/handle ownership, widths, success/error outcomes and relevant
interference. The specification of `chroot`, a capability operation or a cgroup
write describes that operation, not a successful sandbox.

Settle the native implementation route in the first assignment. The existing C
helper deliberately avoids inherited Lean runtime state after fork
([§AR-lifecycle.entry](AR-lifecycle.md#entry-disposition-of-every-m1-entry-premise)); moving effectful control to Lean requires evidence about
runtime threads, allocator/locks, signals and the operations after confinement.
Compare a safe fresh Lean worker with a small native admission executor driven
by proved Lean decisions. Retain existing C/source proofs where their checked
interface already serves the guarantee. A full C-in-place route is acceptable
only if the prototype also resolves its source-to-ordinary-Lean connection;
the older general Clight-port/import experiment is not a solved dependency.

The live product must use the proved definition. A native executor's branches,
arguments, ordering and failure handling need a source proof and checked
connection. One-syscall FFI contracts must expose exact marshaling/ownership and
remain enumerated runtime assumptions. Neither a trusted multi-operation
executor nor a standalone hand-translated model meets this target. Keep the
proof-integrity rule; do not waive it to settle the implementation choice.

For the host boundary, prefer moving security decisions into the executable Lean
library, with Python retaining process/socket/filesystem integration. Its effect
adapter still needs correspondence; passing a verified plan to an unchecked
interpreter is not a complete proof. Measure this approach at an actual host
caller before committing to a broad rewrite. If the Python adapter would require
a new language-semantics project, move the security-relevant effect sequencing
into Lean as well and reduce Python to the public calling interface. Account for
that remaining interface explicitly. Do not make a new Python verifier an
unassigned prerequisite. Preserve public APIs and replace one live path at a
time, keeping historical proofs at their recorded revisions.

Use a source-connected invariant over every permitted execution prefix, including
external failure, cancellation and loss. Unsupported external operations must
not eliminate the executions the proof is meant to cover. Check a useful allowed
execution and real failure paths to establish nonvacuity. State safety separately
from termination under scheduling, finite interference and primitive-progress
assumptions. Composition between proof assistants needs a checked connection under
[§AR-verification.composition](AR-verification.md#composition-proof-obligations-at-boundaries), using the existing bridge where it applies.

Each delivery supplies a machine-checked contract, its source/caller binding,
explicit premises and one integrated consumer. Its ownership premises are
concrete interface requirements with named producers in the coverage map.
Subsequent deliveries prove the producers. Final composition discharges all
application premises; Linux/runtime premises remain explicit. New proof files
live under functional paths such as `verification/launch/` or
`verification/supervision/`, with corresponding shared Lean modules.

## admission: Fail-closed native guest admission

**Before/after:** guest entry is exercised in the VM; this delivery proves that
the actual entry path cannot execute a workload before its required handle,
credential, no-new-privileges and filter operations have succeeded. Setup failure
cannot fall through to execution. `check` has a separate no-workload path.

**Code and consumer:** `guest`, `credentials`, `reset_signals`, their error exits,
and the relevant `namespace_init` fork/stop/cgroup-attach/resume and preflight
branches in `linux/workspace.c`. Reuse the checked filter and child-failure
reporting results. The native launch contract is consumed by the controller's
admission model and by the later workspace/lifetime composition.

Define the value-carrying entry state in [§FS-linux-product.proofs.entry](../functional-spec/FS-linux-product.md#proofsentry-establish-actual-state-at-workload-entry). Receipt
labels alone cannot establish the actual authority or distinguish the wrong UID,
descriptor, filter, argv or limit from the requested one.

**Inputs:** owned, correctly classified descriptors and argument memory, the
prepared root and run identity, primitive process/credential/filter contracts.
Prove descriptor alias restrictions and local fork/handshake conditions at the
actual caller; workspace preparation supplies the remaining root/identity
premises under [§AR-application-verification.authority](AR-application-verification.md#authority-policy-authorized-workspace-construction). Do not assume the guest
already has restricted credentials, handles or the desired filter.

**Acceptance:** a source-connected theorem for the complete admission interface,
covering every setup exit, unexpected return and permitted loss; actual caller
connection; a checked useful entry witness and rejection/failure witnesses;
an audited connection to the executable filter; affected VM setup/preflight
cases on the final changed inputs. The main uncertainty is expressing the real
effectful caller and memory state, addressed first under
[§AR-application-verification.next](AR-application-verification.md#next-first-assignment-and-early-route-decision).

## host: Safe host boundary for arbitrary VM output

**Before/after:** snapshots and returned files are tested Python paths; this
delivery proves the host handles hostile request/filesystem/channel bytes
without granting writes outside a fresh owned run directory or exceeding the
specified byte/file bounds. It also supplies the frozen snapshot producer for
[§AR-application-verification.authority](AR-application-verification.md#authority-policy-authorized-workspace-construction).

**Code and consumer:** `snapshot`, per-run bundle/image construction, `Decoder`,
`parse_export`, `write_exports`, `_known_report`, `_validate_result`, `_publish`
and `report`, through both public CLI and `Workspace` callers. Reuse the shipped
Lean policy validator, while the full byte-to-policy interpretation proof is
assigned under [§AR-application-verification.authority](AR-application-verification.md#authority-policy-authorized-workspace-construction). Move decisions into the
shared executable core where this reduces the source proof burden; account for
the actual Python effect adapter instead of trusting the whole package.

**Acceptance:** for arbitrary VM output, acceptance implies request/bundle
identity matches, complete unambiguous framing, bounded consistent
captures/exports, safe fresh-directory writes and nonreplacement of other runs.
Malformed/truncated transport cannot publish complete artifacts. Snapshot
identities describe the copied bytes, without assuming an atomic view of a
concurrently changing source tree. Storage failure preserves known observations.
Prove the real source/adapter connection and run the affected forged-frame,
snapshot, export and storage scenarios. Existing private-directory ownership
must be explicit, or use descriptor-relative traversal where interference is
permitted. `O_NOFOLLOW` on a final file alone does not protect ancestor traversal.

This guarantee is independently useful and does not depend on correct guest
behavior. A well-formed report from an arbitrary VM still does not establish the
truth of its entry/cleanup fields; [§AR-application-verification.composition](AR-application-verification.md#composition-justified-observations-and-the-complete-public-request)
supplies their trusted provenance. VM reaping is supplied by the host ownership
part of [§AR-application-verification.lifetime](AR-application-verification.md#lifetime-owned-descendants-limits-and-cancellation). The main uncertainties are the
host effect adapter and memory-bounded streaming through the proved core.

## authority: Policy-authorized workspace construction

**Before/after:** the native admission contract receives a prepared root and
identity; this delivery proves the application constructs those inputs from the
accepted policy and frozen snapshots with only the authorized access.

**Code and consumer:** policy JSON decoding, the controller's `planArgs` and invocation setup;
`allocate_identity`, `prepare_resources`, `record_identity`, `bind_at`, `construct_root`
and native import/handle preparation in `linux/workspace.c` and
`linux/artifacts.h`. Discharge the preparation premises of
[§AR-application-verification.admission](AR-application-verification.md#admission-fail-closed-native-guest-admission). Include VM-init request decoding and
controller handoff. Use the host snapshot producer in
[§AR-application-verification.host](AR-application-verification.md#host-safe-host-boundary-for-arbitrary-vm-output).

**Acceptance:** actual policy fields determine the native arguments and granted
objects; leases, aliases, mounts and inherited handles preserve the supported
authority; malformed snapshots, allocation failure and interference fail closed
with justified cleanup observations. Connect the maintained source to the
existing workspace/handle model, including private writable workspace and
read-only runtime. Replay affected useful filesystem and denial cases.

Prove which argv, limits, export choice and digests the caller's bytes denote.
The existing `decodePolicy_*` theorems constrain accepted values but do not prove
the recursive `partial` JSON parser's interpretation. Replace that opaque
boundary with a total executable parser or an equivalently checked parsing
connection, including rejection and all existing bounds. Preserve the versioned
policy format; no new general-purpose policy language is needed.

**Principal risk:** path/object identity under races, descriptor aliases and
partial setup. Primitive filesystem/namespace contracts must expose these cases;
hash equality alone cannot supply authority or ownership.

## lifetime: Owned descendants, limits and cancellation

**Before/after:** admission establishes the run; this delivery proves that the
actual supervision path applies resource/cancellation decisions to its owned
descendants and reports only justified exit/cleanup observations.

**Code and consumer:** native `namespace_init`, main poll/wait/signal loop,
`capture`, accounting and `cleanup`; the Lean controller's wait/loss handling;
the VM init's `helper_child`, `cancel_helper`, `command`, `scopes_extinct`; and
the host runner's QEMU process-group ownership, cancellation and reap paths.
The host/VM adapters are part of this guarantee, not a final integration surprise.
The observation contract feeds [§AR-application-verification.composition](AR-application-verification.md#composition-justified-observations-and-the-complete-public-request).

**Acceptance:** owned identities survive PID reuse/races; each installed limit
and application-side output bound has its stated semantics; cancellation targets
only owned scopes; failed or interrupted cleanup cannot become confirmed cleanup.
Separate guest exit, inner cleanup and VM teardown in source-connected contracts.
Prove finite-prefix safety for hostile children, signal/exit races and process
loss; state explicit progress assumptions for eventual teardown. Exercise the
affected cancellation, limit, output-failure and death cases in the VM.

**Principal risk:** concurrent state and observation provenance. Investigate the
whole cancellation-to-reap interface before extending isolated loop lemmas.

## composition: Justified observations and the complete public request

**Before/after:** a caller receives the tested result/artifacts; this delivery
proves their inner execution/cleanup facts and contents follow from the run's
trusted observations. Compose this with the host boundary and preceding
guarantees to establish [§FS-linux-product.proofs.application](../functional-spec/FS-linux-product.md#proofsapplication-the-complete-application-guarantee).

**Code and consumer:** VM-init result framing and export; native export;
the Lean decoder, detailed report and storage path; host `Decoder`,
`parse_export`, `write_exports`, result validation, publication and retrieval.
Reuse the existing native sender/ordinary Lean decoder connection. Cover both
directions of [§AR-workspace-vm.channel](AR-workspace-vm.md#channel-separate-trusted-framing-from-guest-output) and both CLI/library callers.

**Acceptance:** prove private-channel separation and preservation of
known facts across malformed/truncated/duplicate frames, guest-controlled bytes,
storage errors and retrieval. No valid report may acquire execution or cleanup
facts merely because the VM exited. Prove the VM-init sender and remaining
controller/native export/report paths; consume the host boundary, lifetime
observations and preparation inputs.

**Principal risk:** truthful inner observations across all forwarding and
publication failures. Resolve the VM-init/controller implementation approach at
the start of its assigned code work using a real round trip, reusing the earlier
route decision; final composition must not hide a new source-language project.

The coverage map assigns every reachable application function to a proved
component, an explicitly justified non-security operation, or remaining work.
Connect `check`, `run`, `report` and reusable library paths. Supply all component
preconditions at real call sites, including ABI/memory/handle and host/VM
ownership. Application components cannot remain wholesale trust assumptions in
the final claim. Bootstrap, primitive platform, cryptographic and compiler/runtime
assumptions stay precisely enumerated; physical deployed-binary correspondence
and kernel implementations remain selected M6 work.

**Composition acceptance:** the composed theorem and transitive assumption audit; source and
bundle bindings for every included component; inhabited useful requests and
failure/loss traces; one affected public acceptance run for the identified
bundle. Update the claim manifest to advertise exactly this guarantee. Interface
composition is built with each preceding delivery; this final task must not hide
unassigned controller, Python or C verification work.

## next: First assignment and early route decision

Deliver [§AR-application-verification.admission](AR-application-verification.md#admission-fail-closed-native-guest-admission) from the current `main`, preserving
the working public interface and accepted proofs. The assigned result is the
complete native admission guarantee with its real caller connection.

1. Map the exact guest/preflight call graph, inputs and remaining producer
   obligations. State the value-carrying entry contract and source execution
   theorem before accumulating lemmas.
2. Bound the initial route investigation to four working hours. Inspect the
   pinned Lean runtime's fork/thread/signal constraints and check them only in
   the disposable VM. Exercise one real caller-to-entry/failure path with both
   execution and a kernel-checked proof over primitive effects. Use Velvet only
   if its pinned interface fits. This bounds the decision work, not the complete
   proof assignment; do not spend days on another general importer.
3. Record a concrete route decision in the architectural decisions: safe Lean
   worker, small proved native executor, or existing C with a demonstrated
   checked Lean connection. Include any runtime premise and the exact adapter
   verification work. A prototype is internal evidence for that decision, not a
   completed delivery. If it fails, change the approach to the same entry
   guarantee. Escalate only a specific architecture/scope choice needing the
   user; supply options, evidence and a recommendation.
4. Complete all paths, caller integration, nonvacuity and required acceptance.
   Own `verification/launch/`, affected shared Lean contracts, and the narrow
   native source/caller changes required by this result. Keep public behavior
   stable unless the source proof exposes a bug; specify and fix such a bug.
   Give shipped test-fault selectors an explicit disposition: isolate them in
   a test build or cover every enabled mode in the theorem. Keep test-build
   differences traceable to the product; do not assume a branch is unreachable
   because its name says test. Do not rename compatible policy/ABI identifiers
   solely because they retain historical milestone names.
5. Use [§AR-tooling.checks](AR-tooling.md#checks-one-development-gate): focused checks during work and one final affected
   handoff gate, reusing unchanged foundation/reporting evidence. Commit and push
   the integrated result. Report the new guarantee, its consumer and next action.

Do not promise a duration for all of M5 from M4's product delivery time. Use the
first complete source-connected admission result to estimate the following
deliveries, and revise their implementation routes without moving their promised
guarantees. Ordinary supporting lemmas and tooling remain inside each assignment.
