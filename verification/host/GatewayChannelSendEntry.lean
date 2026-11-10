import GatewayChannelReceives

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {ticks : List (ActorTick runtime)} {pair : Pair}

-- §AR-host-boundary.interfaces.gateway: The checked C prefix supplies the
-- original allocation-lifetime key and exact pending send operands. This
-- consumer selects the SDK-entry row, independently of every future reply.
def native_send_entry
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    {position : Nat}
    (selected : SelectedNativeCut process child native hostUid before after callers next ticks position)
    (_actual : selectNativeCut journal position = some selected)
    (call : NativeCallAt native selected.tick selected.cut.priorNative selected.cut.nextNative)
    (embedded : embeddedNative selected.cut.current = some call)
    (code : NativeCode.CallRow) (interpreted : NativeCode.Interprets code call)
    (source : NativeCode.SourceKey) (sourceProcess : code.process = source.process)
    (headers : source.actionsLifetime ≠ source.attributesLifetime)
    (primitiveEntry : Nat) (ordered : source.entryPosition ≤ primitiveEntry ∧ primitiveEntry ≤ position)
    (descriptor extent flags : UInt64) (bytes : ByteArray)
    (operands : code.operation = NativeCode.encodeOperation (.send descriptor bytes extent flags))
    (amount : extent.toNat = bytes.size) (sender : Side) (handle : Handle)
    (input : call.beforeReferences.handles descriptor = some handle)
    (endpoint : handle.object = pair.endpoint sender) :
    NativeWriteEntry process child native hostUid before after callers next ticks pair := by
  have operation := interpreted.operation
  rw [operands, NativeCode.operation_roundtrip] at operation
  exact {
    position
    tick := selected.tick
    cut := selected.cut
    call
    embedded
    code
    interpreted
    source
    sourceProcess := sourceProcess.symm.trans interpreted.process
    sourceEntry := Nat.le_trans ordered.1 ordered.2
    headers
    primitiveEntry
    primitiveOrder := ordered
    descriptor
    bytes
    extent
    flags
    operation := (Option.some.inj operation).symm
    amount
    sender
    handle
    input
    endpoint }

theorem native_send_entry_actual
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    {position : Nat}
    (selected : SelectedNativeCut process child native hostUid before after callers next ticks position)
    (actual : selectNativeCut journal position = some selected)
    (call : NativeCallAt native selected.tick selected.cut.priorNative selected.cut.nextNative)
    (embedded : embeddedNative selected.cut.current = some call)
    (code : NativeCode.CallRow) (interpreted : NativeCode.Interprets code call)
    (source : NativeCode.SourceKey) (sourceProcess : code.process = source.process)
    (headers : source.actionsLifetime ≠ source.attributesLifetime)
    (primitiveEntry : Nat) (ordered : source.entryPosition ≤ primitiveEntry ∧ primitiveEntry ≤ position)
    (descriptor extent flags : UInt64) (bytes : ByteArray)
    (operands : code.operation = NativeCode.encodeOperation (.send descriptor bytes extent flags))
    (amount : extent.toNat = bytes.size) (sender : Side) (handle : Handle)
    (input : call.beforeReferences.handles descriptor = some handle)
    (endpoint : handle.object = pair.endpoint sender) :
    ActualNativeWrite journal (native_send_entry journal selected actual call embedded code interpreted source
      sourceProcess headers primitiveEntry ordered descriptor extent flags bytes operands amount sender handle input endpoint) := by
  exact actual

end LeanCage.Host.PrivateStreams
