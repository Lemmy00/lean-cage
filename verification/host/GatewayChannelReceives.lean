import GatewayChannelHistory
import FilesystemNativeCodeRows

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {ticks : List (ActorTick runtime)} {pair : Pair}

-- §AR-host-boundary.interfaces.gateway: Decode the operands and product of
-- this exact stored native call; selecting an equal foreign tick is insufficient.
theorem actual_native_read_entry
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    {position : Nat}
    (selected : SelectedNativeCut process child native hostUid before after callers next ticks position)
    (actual : selectNativeCut journal position = some selected)
    (call : NativeCallAt native selected.tick selected.cut.priorNative selected.cut.nextNative)
    (embedded : embeddedNative selected.cut.current = some call)
    (code : NativeCode.CallRow) (interpreted : NativeCode.Interprets code call)
    (descriptor extent flags : UInt64) (bytes : ByteArray)
    (operands : code.operation = NativeCode.encodeOperation (.receive descriptor extent flags))
    (committed : code.product = NativeCode.encodeProduct (.received bytes))
    (receiver : Side) (handle : Handle)
    (input : call.beforeReferences.handles descriptor = some handle)
    (endpoint : handle.object = pair.endpoint receiver) :
    ∃ entry : NativeReadEntry process child native hostUid before after callers next ticks pair,
      ActualNativeRead journal entry ∧ entry.position = position ∧ entry.code = code ∧
      entry.descriptor = descriptor ∧ entry.bytes = bytes ∧ entry.receiver = receiver := by
  have operation := interpreted.operation
  rw [operands, NativeCode.operation_roundtrip] at operation
  have source : call.operation = .receive descriptor extent flags := (Option.some.inj operation).symm
  have product := interpreted.product
  rw [committed, NativeCode.product_roundtrip] at product
  have received : call.product = .received bytes := (Option.some.inj product).symm
  let entry : NativeReadEntry process child native hostUid before after callers next ticks pair := {
    position
    tick := selected.tick
    cut := selected.cut
    call
    embedded
    code
    interpreted
    descriptor
    extent
    flags
    bytes
    operation := source
    product := received
    receiver
    handle
    input
    endpoint }
  refine ⟨entry, ?_, rfl, rfl, rfl, rfl, rfl⟩
  change selectNativeCut journal position = some ⟨selected.tick, selected.cut⟩
  exact actual

-- §FS-host-boundary.caller: Source byte observations keep the full physical
-- input references and the exact committed product, independently of an ACK.
theorem actual_native_read_product
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    (entry : NativeReadEntry process child native hostUid before after callers next ticks pair)
    (actual : ActualNativeRead journal entry) :
    selectNativeCut journal entry.position = some ⟨entry.tick, entry.cut⟩ ∧
      embeddedNative entry.cut.current = some entry.call ∧
      entry.code.product = NativeCode.encodeProduct (.received entry.bytes) ∧
      entry.code.operation = NativeCode.encodeOperation (.receive entry.descriptor entry.extent entry.flags) := by
  refine ⟨actual, entry.embedded, ?_, ?_⟩
  · exact (NativeCode.product_exact entry.interpreted.product).symm.trans (congrArg NativeCode.encodeProduct entry.product)
  · exact (NativeCode.operation_exact entry.interpreted.operation).symm.trans
      (congrArg NativeCode.encodeOperation entry.operation)

end LeanCage.Host.PrivateStreams
