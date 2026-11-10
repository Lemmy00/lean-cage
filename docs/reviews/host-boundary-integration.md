# Host boundary integration work record

This is supporting implementation/evidence for [§AR-host-boundary.acceptance](../architecture/AR-host-boundary.md#acceptance-integrate-before-advertising-the-guarantee)
and [§FS-host-boundary.acceptance](../functional-spec/FS-host-boundary.md#acceptance-prove-and-consume-the-real-host-implementation). M5.2 is not complete. The accepted M5.1
delivery remains on `main`; new host work is isolated on `milikic/host-boundary`.

The maintained C gateway and shared Lean host engine have exercised actual
constructor, policy validator, check/run, frozen Unicode tree/stdin, bounded
transport, artifact validation, publication and retrieval. A useful check took
6.93 seconds; useful execution, inner report-storage failure and channel-loss
cases took 9.80, 9.87 and 8.78 seconds in the designated disposable VM. These
are focused integration observations on a derived development bundle, not a
final bundle acceptance or a proof of the complete host guarantee. The ordinary
Python public implementation remains available during migration.

The implementation/proof connection exposed a real private-path failure. In
the derived test bundle, selecting the installation key as stdin let the VM
return its matching digest. Only the digest comparison is recorded. See the
decision under [§DA-host-engine.private](../decisions/architectural/DA-host-engine.md#private-enforce-private-state-through-caller-paths-and-actual-object-checks).
The earlier successful integration does not support private-state separation.
SourcePaths and fresh reserved roots replace this route; snapshot source proofs
and their evidence are reopened for that relevant implementation change.

The corrected development caller subsequently rejected direct and marked aliases
of private inputs and completed a useful VM execution/publication/retrieval.
`SourcePathsNative.lean` additionally ran the actual native filesystem adapter in
a fresh owned fixture: it retained the original working directory, renamed its
ancestor, replaced the old pathname with different bytes, then copied the
original input through the retained descriptor. The replacement remained
distinct. This evidence is in `.tools/host/source-paths-native.json` and its
identified executable; it is supporting evidence, not final acceptance.

The native public-name candidate now preserves manual `Outcome` construction
and mutation, including current nested values when rendering JSON. These are
presentation records; callers cannot feed them into publication. Its actual
`leancage.native` library and native CLI projection exercised useful execution,
export, publication/retrieval and malformed/private-input rejection in
`.tools/host/candidate-caller.{py,log,json}`. Later source refinements still
require the final identified bundle gate.

The shared-source application chain now kernel-checks through
`CallerProofs.actual_application_complete`: the actual selected bundle and key
gate, snapshot/budget producer, run/archive creation, actual VM read subsequence,
exact complete framing and EOF, artifact validation, publication preservation
and wire fields have one caller transcript. `FilesystemPrefixes` separately
derives fresh file-write targets across arbitrary loss/interference cuts from
individual syscall contracts. The source connection does not by itself close
physical directory/handle separation or native exchange/result projection.

The active/lost-operation source chain additionally checks through
`EntrypointPrefixCuts.entrypoint_cut`, `Commands.run_prefix_source`,
`CallerPrefixCuts.execute_checked_cut`, `RunPrefixCuts.execute_run_cut`,
`PreparationPrefixCuts.prepare_policy_cut` and
`ValidatorPrefixCuts.validate_copied_cut`. The selected last event stays on the
same real transcript. Earlier allocation, bundle, policy, snapshot and validator
producers are carried only when those earlier calls actually returned. Failed
setup cannot authorize a later phase. The validator's read/wait collection is
proved to contain only its individual runtime effects; it supplies no implicit
whole-helper filesystem frame. Physical actor/capability proofs consume this
chain, including cleanup after a failed write and loss at the current effect.

The physical contract review also identified an invalid interpretation of
`EOPNOTSUPP` as private-attribute absence. Public traversal now accepts only
`ENODATA`; unsupported lookup rejects. The snapshot, retrieval, publication and
run/archive proof graph and scripted cases were reopened for that relevant
change. Logical filesystem object lifetime identities do not assume that finite
device/inode numbers are never reused.

The remaining integrated work is the physical filesystem/handle contract and
its directory/private-role separation producer, scoped authenticated retrieval
origin, complete native caller/exchange/result connection, public alias/build
integration, final theorem/assumption review and affected final acceptance.
Component source/proof tests remain individually
identified; no component receipt is treated as the delivery acceptance.

The native read producer now connects the actual function entry, bounded
receive loop, saved interpreter token, errno capture/restoration and remaining
counter debit on one transcript. Its loop proof retains retries and partial
counts and reconstructs the actual initialized buffer. The application
readiness dependency is now supplied by `GatewayReadyActual`. Complete source receipts
for `host_control` and `host_now` retain the actual caller regions, full buffer
permissions and native ownership through their real allocations, API calls
and frees; neither helper consumes response bytes. The clock receipt supplies
memory/thread preservation, with timing semantics assigned to M5.4.
The full readiness receipt composes actual entry, retries and return with the
same control, clock, poll, errno and thread-state observations. It preserves
original data/read-only contents, full stream permissions and every previously
valid native or readable stable capability. The parser result, endpoint
ownership and error/loss source connection remain integration obligations. Direct transport event
classification does not prohibit unrelated callback I/O or establish endpoint
ownership by itself.

The actual caller extraction investigation found a fixed-argument Clight call
rule cannot execute the variadic SDK parser. Frontend acceptance alone had not
established that execution. A fixed-argument object-only parser and tuple/call
adapters replace all reachable variadic calls. The identified source refresh
preserves transport and response helpers and prior identifier bindings;
call-shape and callback fixtures pass. Complete extraction/call ownership
proofs remain in progress.

Caller-source review found borrowed arguments surviving callback-capable
conversions. A path callback can clear the original keyword dictionary and
release a later argument before use. The corrected C entries root all parsed
arguments before callbacks and release those roots on every exit. The native
`PyObject_Call` regression mutates the same dictionary, forces collection and
checks error releases; Python keyword copying is not used to mask the case.
The canonical source refresh preserves all 53 retained helper ASTs and prior
identifier bindings. These supporting results still require the complete
caller/parser/ownership join and identified final bundle acceptance.

The native initialization connection retains relocated descriptor and name
regions beside the live CPython heap. Review found the old World-only release
law inconsistent when distinct references alias one cached object. Its checked
counterexample and transitive invalidation are preserved in
`assurance/host-reference-ownership-amendment.json`; the original construction
record is unchanged and cannot support acceptance. The replacement source-owned
ledger lifts every physical prefix, including invalid and loss states, and
erases to the same machine. `GatewayModuleReferenceDispatch` uses the same actual
`PyType_FromSpec` operation, exact source spec/slots and a scoped reference-count
effect. `GatewayModuleReferenceStore` follows its returned reference through
the actual temporary and C-global store. The source AddObjectRef adapter now
conserves the active and retired reference pool and retains the actual class
cell on both statuses. Its supporting review is
`assurance/host-module-reference-review.json`. Failed FromSpec pool retention
is a separate narrow primitive supplement. The complete preceding initializer
and public getter/result joins still require composition with this repaired interface.

The loader connection starts at actual bootstrap entry and its two allocations,
uses the real `dladdr` primitive result and reads its actual `Dl_info.dli_fname`
field. The filename's string extent and permissions, rather than its pointer
alone, justify dereferencing and C pointer tests through permitted interference.
The source success prefixes reach the actual loaded-path length/comparison
calls, `realpath`, and canonical length/comparison calls with their real inputs.
The primitive comparison decides the actual retained suffix bytes; `realpath`
requires distinct source/destination buffers and preserves only input regions
outside its writes. Failed loader, oversize and nonzero comparison branches
retain their real rejection behavior. The source literals, unsigned arithmetic,
prefix/terminator/suffix copy effects and exact copy statements are checked;
`GatewayBootstrapCopies.actual_bootstrap_copy_sequence` now composes all five
actual memcpy calls, the terminating root byte and the final two-local return
into exact retained root, engine and default-results strings. The loader storage
producer selects the actual buffers/literals; it excludes CPython-managed
`PyModuleDef` storage from C-private ownership.
`GatewayBootstrapGuarantee.actual_bootstrap_call_return` now composes the complete
actual helper call, source entry/allocation, loader and all guard/error cases
through that final return. The result retains both path validations, historical
loader/canonicalization observations and exact strings/capacities. The at-load
adapter derives its initial storage instead of assuming initialized paths.
`assurance/host-bootstrap-source-review.json` preserves the full type/axiom audit.
`GatewayBootstrapDescriptors.actual_loaded_bootstrap_descriptors` additionally
retains all initialized descriptor/literal regions through that same complete
helper. Its checked adapters restrict write authority while retaining reads from
actual readonly ELF objects. The separate at-load readonly permission observation
and every real write footprint derive the frame; no whole-procedure retention
premise supplies it. `GatewayInitializationBootstrap` derives bootstrap Return0
from the actual initializer call and failure guard for a non-null final return.
`assurance/host-bootstrap-retention-review.json` records these full statements.
The preceding guarded initializer prefix, later CPython/class/reference effects
and public-call composition remain pending; these results are supporting work
inside M5.2.

External host callbacks use the versioned authority scope in
[§DA-host-engine.hostcode](../decisions/architectural/DA-host-engine.md#hostcode-identify-the-external-host-code-authority-profile). Same-UID private-file access and trusted-parent
authority reconfiguration are not denied by mode bits. Permitted public
callback effects need their actual native-caller operation rows in the same
physical history; the pending composition cannot substitute a whole callback
private-state frame or preallocate future IPC birth identities.

`NativeCode` supplies the separate shared operation/reply/product data boundary.
Its strict kernel import is checked without changing the existing gateway,
spawn or bootstrap datasets. The ordinary decoder checks every machine word and
byte before projecting into native kernel operations. The checked additive
extension preserves all Native94 declarations and adds shared `SourceKey` and
`CallRow` records. A later checked extension preserves those 100 fingerprints
and adds 27 dependencies for the pure full-table channel observer; the frozen
shared export now contains 127 declarations.
`GatewayNativeRows.gateway_actual_spawn_row` binds the SAME
actual pending source argument list and SDK call to its primitive row, retaining
the entry order, process lifetime and distinct fresh SDK-header lifetimes.
`FilesystemNativeCodeRows.bindSourceRow` consumes the exact shared fields and
one actual global `NativeCallAt`; both full parent reference/CWD snapshots are
canonical encodings of that call. Reply and committed product remain separate.
`GatewayExchangeNativePrepared.actual_exchange_entry_pending_native` derives
the same first pending spawn, argument vector and four IPC leases from actual
entry and setup. Its physical-row observer requires no eventual SDK return or
acknowledgement. `FilesystemNativeLaunchHistory` selects the actual birth and
later exec from the same global history before handoff; per-row interpretations
bind those exact cuts. `GatewayNativeChannels` derives channel evidence from
the real child file actions and full exec snapshot, consumed by
`FilesystemNativeExecRows.actual_exec_binding`. The remaining application join
must supply those same two row interpretations and actual IPC object kinds.

`GatewayBootstrapHistory` additionally carries the aggregate active and retired
reference pool through the complete actual bootstrap; aliased pointer credits
are counted together. `GatewayInitializationHistory` consumes it at the real
initializer bootstrap guard. `GatewayDictionaryCallReceipts`,
`GatewayDictionarySecondReceipt`, `GatewayDictionaryInsertReceipt` and
`GatewayDictionaryReleaseReceipts` select the actual key/duplicate/second-child,
insertion and release calls, retaining source prefixes, saved parameters and
continuations. Non-null progress forces the real positive key, zero duplicate
and zero insertion statuses. These are being composed into the recursive
parser fold, not counted as an additional delivery.
`assurance/host-source-connections-review.json` records these statements and
their assumptions; complete initialization, response provenance and physical
custody composition remain required for M5.2 acceptance.

`GatewayInitializationConnection.gateway_actual_public_bootstrap_connection`
now starts at the real exported `PyInit__host` call and the actual at-load
regions. It derives both real interpreter-query checks, the zero flag checks,
active store, same non-null private initializer and complete bootstrap
execution. Its caller prefix and remaining public suffix retain the actual
nested continuations. Bootstrap returns the validated paths, descriptor
regions, aggregate active/retired reference scope and actual active-one,
completed-zero cells. A separate source proof shows that a null private-body
return stays null through the public clear/return path. These results and
their individual primitive inputs are recorded in
`assurance/host-initialization-connection-review.json`. The following
import/attribute/class/module operations must still supply the actual post-body
reference and region context. `GatewayInitializationCompletion` now consumes
that normal context and source-owned module at the real wrapper return: its
source pointer check, completed-one store, active-zero store and same module
return retain the current regions and aggregate pool. `GatewayInitializationFailure`
separately consumes the actual null-body continuation under a rooted attached
native-memory discipline, permits a pending exception, and derives active-zero
with the previous completed cell unchanged. It claims no successful module graph
on that branch. The full types and inputs are recorded in
`assurance/host-initialization-returns-review.json`; the post-body producers and
actual public-callback consumers remain required.

`GatewayPublicInitializationCaller.gateway_actual_uninitialized_callback`
starts at the real exchange, path, workspace-constructor or CLI call. Actual
entry allocation retains the flag cells; source allocation also proves the
global names are not shadowed by locals. Completed-zero routes to the actual
error-posting body and excludes every other external operational callee,
without requiring a later method return. The completed-one source prefix
retains its exact loaded word and original function tail. These callback
consumers and their initializer-context adapter are recorded in
`assurance/host-public-initialization-review.json`.
`GatewayAttachedNative` supplies only attached ambient and native stack
allocate/store/free representation laws for these quiet source phases. It adds
no SDK callback frame or clear-exception requirement. The previous broader
supporting return record is preserved in
`assurance/host-initialization-native-projection-before.json.gz`.

`GatewayJsonNumberSourceConnection.gateway_actual_json_number_constructor`
connects a real numeric-helper call to its first actual constructor and the
remaining suffix. The same retained input bytes supply the complete valid
JSON-number grammar, exact sign/digit/integer-end/index temporaries and actual
Long0 or UTF8 arguments. Its source proof includes the real integer do/while,
fraction/exponent scans and all syntax-error exits. Per-byte retention and the
65536-byte bound are explicit inputs from scalar storage; constructor/reference
semantics and the complete recursive parser are the consumers in progress.
`assurance/host-number-source-review.json` records the full types, transitive
assumptions and exact C/Clight/source bindings. This is supporting integration
inside M5.2.

M5.3 subsequently supplies policy/authority producers, M5.4 owned lifetime and
limits, and M5.5 truthful observation provenance. The host theorem must permit
arbitrary VM bytes independently of those later guest-truth producers.

The current guarded caller source is C `8dc2bdd9b0a45478` / Clight
`2fce74e393b92115`. Its exact previous function-body tails remain unchanged.
The outgoing readiness proof derives request-channel silence from the actual
distinct control descriptor, then feeds the real sender and source-built header.
Its generated projection proofs reuse the maintained source decompositions;
`verification/host/outgoing_proofs.py` is untrusted and each emitted declaration
is kernel checked. Initializer timing evidence is corrected in
`assurance/host-initializer-timing-correction.json`: pre-module_from_spec return
visibility did not establish pre-PyInit return visibility. Native entry guards
are checked independently against the maintained C functions.

The post-bootstrap initializer now has checked actual-source frontiers through
import, attribute lookup, library release, module creation and all three class
publications. `GatewayInitializerImport.gateway_actual_initializer_import`
extracts the same real SDK call and reference from the bootstrap suffix; the
actual later NULL guard establishes the required non-null result. The shared
source literals supply its `pathlib` bytes. `GatewayInitializerGlobalStores`
extracts actual pointer writes without assuming vacant globals or reusing a
loader boundary. The reference-history adapters account for prior overwritten
owners, including NULL replacement during retry.

`GatewayInitializationRejectionBoundary` connects the actual active/completed
checks to their error-return barriers before any other pending external call,
without an eventual callback return. The full-program inventory identifies the
sole direct class-cell writer and its caller, and checks that class-cell
addresses are unexposed. The sole indirect C call belongs to Outcome traversal;
its SDK visitor capability remains explicit. This syntax inventory does not
replace indirect-store or nested SDK callback authority proofs.

The complete quantified source, individual initializer SDK/reference laws,
rejection and inventory interfaces and their transitive assumptions are recorded
in `assurance/host-initializer-objects-review.json`. These checked inputs feed
the active full initializer/class/reference/callback composition. The SDK laws
supply no class-global memory frame or complete-initializer success premise.
The final module, current regions and callback authority must still be produced
for the existing public completion consumers under
[§FS-host-boundary.caller.initialization](../functional-spec/FS-host-boundary.md#callerinitialization-reject-nested-initialization-before-changing-module-state).
