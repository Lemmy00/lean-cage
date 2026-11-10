# Host source verification

The host delivery follows [§AR-host-boundary.acceptance](../../docs/architecture/AR-host-boundary.md#acceptance-integrate-before-advertising-the-guarantee) and [§FS-host-boundary.acceptance](../../docs/functional-spec/FS-host-boundary.md#acceptance-prove-and-consume-the-real-host-implementation).
The native public gateway is `linux/host_python.c`; the separate maintained Lean engine
owns filesystem, VM transport, validation and publication control. The gateway does
bounded CPython marshaling and invokes only its identified engine. This directory
contains the source connection and its development driver, not a replacement product.

`gateway.py --prepare` translates the actual C file with the pinned Clight frontend
and the actual stable-ABI CPython headers. It records every included SDK/header hash,
then strictly imports the executable Lean bounds, byte codecs and exact request and
response views. Named module arguments compile focused proof leaves against those
generated inputs. A final delivery record must
bind matching native source, SDK, executable Lean definitions, theorem types,
transitive assumptions and the integrated callers; a development pass does not
constitute that final record.

The current source modules separate responsibilities:

- `GatewayMachine` models actual Clight instructions, individual external/builtin
  operations, interference, blocked prefixes and loss, including committed loss.
- `GatewayContexts`, `GatewayCallPath` and `GatewayOperations` cut callbacks and primitive
  occurrences out of the same wider execution. The memory, world, pending waits,
  interference and committed loss are retained. `GatewayReturns` proves constant
  failure returns without assuming that local frees succeed.
- `GatewayPython` states individual bytes/refcount contracts with explicit output
  stores, logical strong roots, readable bytes, GIL state and pending exceptions.
- `GatewayAllocation`, `GatewayPrefix` and `GatewayFieldEntry` derive actual fresh
  local output cells and the exact first CPython call. `GatewayFieldFailure`
  excludes a successful field return after an unsuccessful bytes operation.
- `GatewayFieldGuard`, `GatewayControl` and `GatewayFieldRoot` connect the actual
  output-cell reads, checked native bound, strict executable Lean bound and exact
  object retained by the subsequent refcount operation. `GatewayFieldStorage`,
  `GatewayFieldPublish` and `GatewayFieldFree` construct actual stores and local
  frees from the real layout, independent writable storage and actual API cells.
- `GatewayRegistry` checks actual public method names, flags and function pointers
  in the maintained source tables, resolving source identifiers rather than
  relying on generated string-literal numbers. `GatewayWrappers` proves the actual
  check/run forwarding calls preserve `self`, positional arguments and keywords.
- `GatewayCallShapes` checks every actual maintained call and builtin argument
  count against its source signature. The native object parser uses fixed
  tuple/dictionary APIs and explicit source loops. Fresh tuples and `CallObject`
  carry callback arguments; attribute lookup precedes CLI method calls. The only
  native ABI adapter forwards one `fcntl` operation with its three actual
  arguments. Its C implementation and header belong to the identified inputs.
- `GatewayWords`, `GatewayReads` and `GatewayWordReceipt` connect actual fixed-width
  C loops and initialized memory to the strict shared codec. Readonly siblings
  preserve earlier packet fields through later stores under per-interference
  region ownership, without a whole-helper success assumption.
- `GatewayHeaderRuntime`, `GatewayHeaderWords` and `GatewayHeaderReceipt` connect
  those actual source stores to the coupled interpreter/runtime state. Their
  receipts preserve earlier readonly packet fields, full target permissions and
  existing native/stable capabilities while supplying the shared word encoding.
  `GatewayHeaderPrefix` composes these receipts without freezing future block
  identities or unrelated runtime memory.
- `GatewayRequestCode` proves equality with the actual executable request encoder,
  the structural decoder's equality with its former loop, and both directions
  between raw bounded layout and actual decoder success. Raw layout contains
  individual header words, field slices and full consumption; it does not posit
  a decoded request. The native producer must still supply those facts.
- `GatewayReadEntry`, `GatewayReadGuard` and `GatewayReadTransfer` derive canonical
  function entry, the successful remaining-length guard and the exact successful
  transfer occurrence from one actual read execution. Error setters are called
  on the actual failure path; their success is not assumed to prove the fixed
  failure return. `GatewayReturnTypes` handles arbitrary nested helper results,
  while actual caller tests exclude undefined and unsuccessful outcomes.
- `GatewayReadSource` derives the actual entry-to-guard-to-transfer cut with
  coupled memory/runtime ownership. `GatewayBindings` supplies actual symbol and
  function bindings from the maintained program environment. Its source clients
  can be instantiated without an unrelated function table.
- `GatewayTransferIteration` joins the same saved thread token, receive, errno
  lookup, actual errno load, thread restore and caller suffix. Its receipt retains
  the exact whole-prefix receive bytes, initialized current bytes, existing
  readonly cells and full permissions of the actual stream/data blocks.
  `GatewayTransferCount` derives the exact observed byte count for the entire
  actual transfer, by trace-length induction across partial acknowledgments and
  arbitrary finite retries. EOF, other errors and undefined captured errno cannot
  become a successful positive transfer. `GatewayTransferBuffer` reconstructs the
  complete accumulated buffer through those same iterations, preserving earlier
  received bytes and the original stream/data permissions.
- `GatewayReadCounterSource`, `GatewayReadComplete` and `GatewayReadProducer`
  compose the actual successful transfer with the source counter debit and
  return. The resulting read receipt includes the exact whole-helper receive
  bytes, initialized destination, remaining counter, readonly frame and retained
  native/stable capabilities. `GatewayReadActual` binds this producer to the
  maintained program's actual symbols and layout.
- `GatewayStreamInterface` and `GatewayReadyInterface` name application source
  producers. Their inputs include native
  private-block capabilities and actual writable permissions; these facts are
  distinct. Private capabilities can include fresh future block identities, with
  actual allocation and permissions establishing lifetime. Readiness preserves
  the entire destination and existing rooted response cells across GIL release.
  `GatewayTransferSource` checks the real loop's readiness call and arguments.
  `GatewayReadyEntry`, `GatewayReadyControl`, `GatewayReadyClock`, `GatewayReadySetup`,
  `GatewayReadyIteration`, `GatewayReadyTail` and `GatewayReadyReturn` connect the
  actual allocation, helper calls, timeout, local stores, save/poll/errno/restore,
  signal check, retry and release on the same execution. `GatewayReadyProtected`
  retains original data and every readable stable capability without assuming
  that native and stable regions are disjoint. `GatewayReadyActual` supplies
  readiness and the complete read producer at the actual maintained environment
  from individual thread/runtime contracts. Public caller,
  request construction, spawn and response consumers must use the resulting
  same-execution receipts. This normal-return result does not substitute for the
  separate error-posting, pending-exception and loss-prefix ownership proof.
- `GatewayStackAllocation` and `GatewayExchangeEntry` recover the actual exchange
  allocation and separate header/stream buffers from the same function call.
  `GatewayCancellationInputs` checks the real type slots, ordinary flag offset
  and volatile signal-global binding. Volatile global memory has Clight's
  `Nonempty` permission; its value comes from the explicit volatile primitive.
  `GatewayTypeRuntime` specifies the individual type/new/module operations,
  requiring actual raw specification loads and the real default allocator.
- `GatewaySpawnABI` checks the twelve fixed native resource signatures and the
  actual SDK struct sizes. `GatewaySpawnResources` distinguishes physical slots,
  invocation leases, object/OFD birth histories, peer topology and exclusive
  status. `GatewaySpawnRuntime`, `GatewaySpawnActions` and `GatewaySpawnProcess`
  describe individual socket/duplicate/flag/close, SDK builder and spawn effects.
  A spawned birth can fail before exec; its later exec uses the same recorded
  plan and arguments. Source setup must produce that plan and its real ownership.
  `spawn.py --prepare` strictly imports `GatewaySpawnChannels.ChannelEvidence`
  without changing the frozen byte-codec dataset. The exact conjunction feeds a
  checked Lean adapter into the unchanged `InitialEngineBinding`; importing the
  original proposition structure itself hit the strict elimination rejection.
  The importer remains unchanged and its strict checks remain enabled.
- `GatewayPairActual.actual_private_pair` cuts the actual socketpair operation out
  of the complete native helper execution. Its same birth receipt identifies both
  final array cells after the actual two-iteration duplicate/close/store loop.
  Both FDs are at least four, retain their IPC object/OFD identities and flags,
  and preserve every older caller lease, status and birth-topology observation.
  Thus creating the control pair retains the first data pair. This preservation
  follows from actual fresh objects and source-selected closes; it does not assume
  empty physical FD slots or a whole-helper frame. The selected error paths cannot
  return success. Full error/loss memory and release receipts remain obligations
  of the surrounding caller connection.
- `GatewayCallerBuffers`, `GatewayCallerReadonly` and `GatewayCallerFamily` retain
  real caller-array permissions, immutable payload contents and original native
  and readable stable references. These arrays may still be uninitialized.
  `GatewayCallerClockResources.actual_clock_array_resources` applies the actual
  fresh clock allocation, individual clock operation and real local free to that
  family while retaining earlier descriptor owners. `GatewayPassiveResources`
  supplies only the individual native observer's FD/OFD frame; it supplies no
  clock-helper, memory, byte-stream or progress guarantee.
- `GatewayExchangeConnections.actual_exchange_connections_before_flags` consumes
  one actual exchange-body prefix reaching its selected spawn. It derives the
  real clock guard, both successful pair calls and their exact socketpair
  occurrences in that wider trace. It retains the normalized cells, caller-array
  permissions and descriptor owners through the second pair. No eventual
  method return is required. `GatewayExchangeFlags.actual_exchange_flags_before_sdk`
  then derives the actual successful flag calls and the engine-facing OFD's
  blocking mode before SDK initialization. The earlier full pair status snapshot
  is projected to exact endpoint leases when that intentional mode change occurs.
  `GatewayExchangePrepared.actual_exchange_allocated_spawn` now derives the local
  storage, separation, writable vectors and empty scoped SDK headers from the
  actual allocation. It joins both guarded initializers, process-group settings,
  three descriptor duplicates, closefrom and the six vector stores to the same
  selected spawn. Nonzero setup takes the actual cleanup path even when the
  wider method has no observed return. `GatewayExchangeStart` recovers that
  actual allocation from the original exchange call reaching its selected spawn.
  `GatewaySpawnRecorded` then applies the individual spawn operation to these
  same vectors, preserving caller storage and retaining a possible child birth
  on either status path. Birth and exec views are invocation-filtered; other
  launches remain in the global physical history. The remaining source join
  covers header/payload transmission, response/EOF, reaping and full failure/loss
  memory and release handling.

The native keyword-entry methods immediately retain all parsed object references
before callback-capable conversions. The matching cleanup releases every retained
argument, including setup/conversion errors. The callback integration fixture
uses the public CPython call API with the same mutable keyword dictionary;
ordinary path callbacks clear that dictionary and force collection. This covers
constructor, run/check and single-argument failures plus direct `Outcome` lifetime.
The full source proof must connect the parser's borrowed outputs, the actual
retain loop and later conversions; the behavioral check is supporting evidence.
`GatewayArgumentsActual` now proves the complete actual retain helper and its
native roots, including repeated values and nullable slots. `GatewayKeywordCode`
defines positional/keyword selection and optional defaults independently of C
storage; `GatewayKeywordPlans` checks the actual public name/format tables.
`GatewayKeywordRuntime` contains only individual tuple, dictionary, genuine type,
Unicode-comparison and exception-query operations. It supplies no whole parsing
or caller-extraction success law. The fixed source parser must produce the
selection and initialized output-cell receipt before the root producer is used.
The focused keyword fixture compares accepted and rejected call shapes with the
preceding native API without starting an engine or VM.

`GatewayGlobals` derives individual static-byte initializers from the source
loader. It is not a whole Python initial state: standalone Clight declarations
for linked CPython globals have empty initializers. The actual linked runtime
supplies those object headers, type objects and exception-pointer cells while
the native module's static regions retain their initialized bytes. Native entry
must consume that regional loader/SDK contract and derive its application roots
through the actual type construction, module registration and public methods.
Conjoining live SDK objects with the same full standalone `Genv.init_mem` state
would give the wrong initial boundary.

The whole gateway proof must additionally compose public dispatch and keyword
extraction, constructor configuration, path encoding/decoding, retained field stores,
complete packet construction, descriptor failure handling and fixed spawn arguments,
GIL release/restoration, cancellation/signal ownership, bounded response recursion,
numeric and object construction, exception projection and helper reaping. These are
implementation obligations inside the host delivery. No whole extraction,
exchange, safe-response, cleanup or Python-interpreter premise may substitute for
their source producers. Useful caller executions and every relevant failure/loss
case must remain expressible in the same model.

Individual runtime contracts must distinguish CPython operations (object/type and
argument lookup, filesystem codecs, immutable byte access, allocation/refcount,
container construction, numeric operations, exceptions, thread/GIL state and method
registration) from Linux operations (loaded-artifact identity, clocks, fresh Unix
sockets, descriptor flags/duplication/closure, spawn attributes/actions, signal
handlers, poll/read/write/shutdown, process-group signaling and wait). Their effects
are one operation at a time. The protected bootstrap namespace is the explicitly
scoped platform contract in [§AR-host-boundary.interfaces](../../docs/architecture/AR-host-boundary.md#interfaces-fix-the-data-and-ownership-boundaries-before-parallel-edits); caller data and publication
namespaces receive no such assumption.

A complete typed response plus exact EOF is an owned-engine observation. Its
provenance is separate from the helper's subsequent exit or reaping status.
Cancellation is a one-byte request over the dedicated inherited FD3 channel;
neither sending it nor observing helper exit establishes VM cleanup.

`Outcome` remains directly constructible and its presentation fields remain mutable.
Its read-only `observation` attribute exposes the original received metadata graph
at the initial workspace return, including the exact filesystem-decoded output.
The actual native type specification sets the stable ABI immutable-type flag, so
callbacks cannot replace that getter, the other class descriptors or class methods.
Instance field setters and direct initialization/reinitialization remain available.
This graph is not passed to the customizable path constructor. The output path
field records that actual presentation callback result; a captured class identity
does not freeze its construction methods. Manual/reinitialized outcomes have no
received observation. Subsequent caller mutation remains presentation behavior.
Its native JSON projection snapshots the current fields and recomputes metadata and
SHA256 values, including nested file-map changes. Such caller-created or modified
records are presentation data: no gateway request or publication operation accepts
an `Outcome` object as authority. The returned engine observation is the value at
return, before any subsequent caller mutation.
Each getter, setter and JSON projection holds its selected data dictionary
independently before callback-capable APIs. A getter owns its returned field before
releasing that dictionary; a setter also roots its incoming value. The ordinary
GC and destructor integration fixture reinitializes the same receiver while
those operations run, verifies that selected report values remain alive, and
checks their eventual release. Receiver reinitialization is permitted; the source
does not assume the public receiver remains unchanged across callbacks.

The user-requested partial M5.2 checkpoint is summarized in
[the continuation](../../M5-CONTINUE.md). The preserved source/claim manifests
are component evidence; no complete M5.2 acceptance or default-caller migration
is claimed. A comment-only amendment in
`assurance/host-source-comment-amendment.json` retains the original source and
proves exact equality with the regenerated Clight program. Earlier component
records keep their original input bindings; do not refresh them to suppress a
mismatch. The next aggregate record must consume this explicit amendment.
