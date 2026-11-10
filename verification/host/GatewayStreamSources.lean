import GatewayPrivateStreams
import EntrypointPendingWriter

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

-- §FS-host-boundary.caller: Identity comes from this actual process lifetime,
-- source ordinal, selected global boundary and live descriptor/OFD snapshot.
structure EngineWriteEntry {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (ticks : List (ActorTick runtime)) (pair : Pair) where
  position : Nat
  tick : ActorTick runtime
  selected : ticks[position]? = some tick
  actor : ActorId
  engine : EngineState
  present : tick.before.actors actor = some engine
  running : engine.running = true
  request : Request
  next : Reply → Program UInt32
  head : engine.current = .call (.filesystem request) next
  writing : request.op = .write
  sender : Side
  handle : Handle
  input : engine.references request.first = some handle
  endpoint : handle.object = pair.endpoint sender

def EngineWriteEntry.key {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {ticks : List (ActorTick runtime)} {pair : Pair} (entry : EngineWriteEntry ticks pair) : CallKey :=
  .engine entry.actor entry.engine.events.length

def EngineWriteEntry.description {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {ticks : List (ActorTick runtime)} {pair : Pair} (entry : EngineWriteEntry ticks pair) : WriteDescription :=
  ⟨entry.sender, entry.request.first, entry.handle.object, entry.handle.description, entry.request.left.data.toList⟩

-- §AR-host-boundary.primitives: This source receipt is derived at the pending
-- call. The selected tick may be its peer's recv; no writer ACK is assumed.
theorem engine_write_source {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {ticks : List (ActorTick runtime)} {pair : Pair} {initial : World} {final : Population}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    (entry : EngineWriteEntry ticks pair) :
    Nonempty (EntrypointWriterPrefix.PendingCut entry.engine entry.request) :=
  EntrypointWriterPrefix.pending_write_at journal entry.selected entry.present entry.running entry.head entry.writing

theorem engine_write_arguments {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {ticks : List (ActorTick runtime)} {pair : Pair} (entry : EngineWriteEntry ticks pair) :
    entry.description.descriptor = entry.request.first ∧
    entry.description.object = pair.endpoint entry.sender ∧
    entry.description.description = entry.handle.description ∧
    entry.description.bytes = entry.request.left.data.toList :=
  ⟨rfl, entry.endpoint, rfl, rfl⟩

-- §AR-host-boundary.interfaces.gateway: Select the call stored in the SAME
-- joint row. A second valid call on an equal foreign tick is insufficient.
def embeddedNative {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses} {tick : ActorTick runtime}
    (row : NativeExternalStep process child native hostUid before callers tick after next) :
    Option (NativeCallAt native tick callers next) :=
  match row with
  | .native _ call _ _ => some call
  | _ => none

structure NativeReadEntry {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (process : ProcessContract runtime) (child : ChildPrimitive kernel) (native : NativePrimitive kernel)
    (hostUid : Nat) (before after : Processes) (callers next : NativeProcesses)
    (ticks : List (ActorTick runtime)) (pair : Pair) where
  position : Nat
  tick : ActorTick runtime
  cut : NativeExternalCut process child native hostUid before after callers next ticks position tick
  call : NativeCallAt native tick cut.priorNative cut.nextNative
  embedded : embeddedNative cut.current = some call
  code : NativeCode.CallRow
  interpreted : NativeCode.Interprets code call
  descriptor : UInt64
  extent : UInt64
  flags : UInt64
  bytes : ByteArray
  operation : call.operation = .receive descriptor extent flags
  product : call.product = .received bytes
  receiver : Side
  handle : Handle
  input : call.beforeReferences.handles descriptor = some handle
  endpoint : handle.object = pair.endpoint receiver

-- §FS-host-boundary.ownership: Product, reply and full input table belong to
-- the selected stored call; no observation or completion is invented.
theorem native_read_identity {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
    {ticks : List (ActorTick runtime)} {pair : Pair}
    (entry : NativeReadEntry process child native hostUid before after callers next ticks pair) :
    ticks[entry.position]? = some entry.tick ∧
    entry.call.beforeReferences.handles entry.descriptor = some entry.handle ∧
    entry.handle.object = pair.endpoint entry.receiver ∧
    entry.call.product = .received entry.bytes ∧
    embeddedNative entry.cut.current = some entry.call := by
  have shape := congrArg (fun items : List (ActorTick runtime) => items[entry.position]?) entry.cut.shape
  have inside : (entry.cut.leading ++ entry.tick :: entry.cut.trailing)[entry.position]? = some entry.tick := by
    simp [entry.cut.count]
  exact ⟨shape.trans inside, entry.input, entry.endpoint, entry.product, entry.embedded⟩

-- §AR-host-boundary.interfaces.gateway: These are the exact shared operands
-- and committed bytes of the stored call, ready for the actual C row binder.
theorem native_read_code {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
    {ticks : List (ActorTick runtime)} {pair : Pair}
    (entry : NativeReadEntry process child native hostUid before after callers next ticks pair) :
    entry.code.operation = .receive entry.descriptor.toNat entry.extent.toNat entry.flags.toNat ∧
      entry.code.product = .received (entry.bytes.data.toList.map UInt8.toNat) ∧
      entry.code.beforeReferences = NativeCode.encodeReferences entry.call.beforeReferences := by
  refine ⟨?_, ?_, entry.interpreted.input⟩
  · simpa only [entry.operation, NativeCode.encodeOperation] using (NativeCode.operation_exact entry.interpreted.operation).symm
  · simpa only [entry.product, NativeCode.encodeProduct, NativeCode.encodeBytes] using
      (NativeCode.product_exact entry.interpreted.product).symm

-- §AR-host-boundary.primitives: A native write entry retains raw operands.
-- Its product/reply need not describe a completed SDK call or complete send.
structure NativeWriteEntry {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (process : ProcessContract runtime) (child : ChildPrimitive kernel) (native : NativePrimitive kernel)
    (hostUid : Nat) (before after : Processes) (callers next : NativeProcesses)
    (ticks : List (ActorTick runtime)) (pair : Pair) where
  position : Nat
  tick : ActorTick runtime
  cut : NativeExternalCut process child native hostUid before after callers next ticks position tick
  call : NativeCallAt native tick cut.priorNative cut.nextNative
  embedded : embeddedNative cut.current = some call
  code : NativeCode.CallRow
  interpreted : NativeCode.Interprets code call
  source : NativeCode.SourceKey
  sourceProcess : source.process = call.token
  sourceEntry : source.entryPosition ≤ position
  headers : source.actionsLifetime ≠ source.attributesLifetime
  primitiveEntry : Nat
  primitiveOrder : source.entryPosition ≤ primitiveEntry ∧ primitiveEntry ≤ position
  descriptor : UInt64
  bytes : ByteArray
  extent : UInt64
  flags : UInt64
  operation : call.operation = .send descriptor bytes extent flags
  amount : extent.toNat = bytes.size
  sender : Side
  handle : Handle
  input : call.beforeReferences.handles descriptor = some handle
  endpoint : handle.object = pair.endpoint sender

def NativeWriteEntry.key {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
    {ticks : List (ActorTick runtime)} {pair : Pair}
    (entry : NativeWriteEntry process child native hostUid before after callers next ticks pair) : CallKey :=
  nativeKey entry.source entry.primitiveEntry

def NativeWriteEntry.description {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
    {ticks : List (ActorTick runtime)} {pair : Pair}
    (entry : NativeWriteEntry process child native hostUid before after callers next ticks pair) : WriteDescription :=
  ⟨entry.sender, entry.descriptor, entry.handle.object, entry.handle.description, entry.bytes.data.toList⟩

structure PairBirthEntry {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (process : ProcessContract runtime) (child : ChildPrimitive kernel) (native : NativePrimitive kernel)
    (hostUid : Nat) (before after : Processes) (callers next : NativeProcesses)
    (ticks : List (ActorTick runtime)) (pair : Pair) where
  position : Nat
  tick : ActorTick runtime
  cut : NativeExternalCut process child native hostUid before after callers next ticks position tick
  call : NativeCallAt native tick cut.priorNative cut.nextNative
  embedded : embeddedNative cut.current = some call
  code : NativeCode.CallRow
  interpreted : NativeCode.Interprets code call
  first : UInt64
  second : UInt64
  operation : call.operation = .socketPair 1 526337 0
  product : call.product = .socketPair first second
  firstHandle : Handle
  secondHandle : Handle
  firstInput : call.afterReferences.handles first = some firstHandle
  secondInput : call.afterReferences.handles second = some secondHandle
  callerObject : firstHandle.object = pair.caller
  engineObject : secondHandle.object = pair.engine
  callerFresh : tick.before.shared.allocated pair.caller = false
  engineFresh : tick.before.shared.allocated pair.engine = false

end LeanCage.Host.PrivateStreams
