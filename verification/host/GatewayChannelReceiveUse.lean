import GatewayChannelReadSelection
import GatewayChannelCode

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {ticks : List (ActorTick runtime)} {pair : Pair}

-- §AR-host-boundary.interfaces.gateway: The original source's exact receive
-- row gives the canonical stored-call byte projection, including empty/lost
-- products. Descriptor numbers are interpreted in THAT full input table.
theorem source_receive_matches_stored_row
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    (use : ChannelCode.ReceiveUse) (source : use.Consistent) (endpoint : use.dataObject = pair.caller)
    (point : SelectedNativeCut process child native hostUid before after callers next ticks use.position)
    (selected : selectNativeCut journal use.position = some point)
    (call : NativeCallAt native point.tick point.cut.priorNative point.cut.nextNative)
    (embedded : embeddedNative point.cut.current = some call)
    (interpreted : NativeCode.Interprets use.row call) :
    (nativeCallerBytesAt (pair := pair) journal use.position).map UInt8.toNat = use.bytes := by
  classical
  obtain ⟨formed, process, order, descriptor, positive, extent, operation, reference, product⟩ := source
  have descriptorWidth : use.descriptor < 2 ^ 64 := by omega
  have extentWidth : use.extent < 2 ^ 64 := by omega
  have codeOperation : use.row.operation = NativeCode.encodeOperation
      (.receive (UInt64.ofNat use.descriptor) (UInt64.ofNat use.extent) 0) := by
    simpa only [NativeCode.encodeOperation, UInt64.toNat_ofNat_of_lt' descriptorWidth,
      UInt64.toNat_ofNat_of_lt' extentWidth, UInt64.toNat_zero] using operation
  have actualOperation := interpreted.operation
  rw [codeOperation, NativeCode.operation_roundtrip] at actualOperation
  have op : call.operation = .receive (UInt64.ofNat use.descriptor) (UInt64.ofNat use.extent) 0 :=
    (Option.some.inj actualOperation).symm
  obtain ⟨codeHandle, codeInput, codeObject, codeDescription⟩ := reference
  rw [interpreted.input] at codeInput
  simp only [NativeCode.encodeReferences, descriptorWidth, ↓reduceIte] at codeInput
  cases actualInput : call.beforeReferences.handles (UInt64.ofNat use.descriptor) with
  | none => simp only [actualInput, Option.map_none] at codeInput; cases codeInput
  | some handle =>
    have sameHandle : NativeCode.encodeHandle handle = codeHandle := by
      simpa only [actualInput, Option.map_some, Option.some.injEq] using codeInput
    have actualObject : handle.object = pair.caller :=
      (congrArg NativeCode.Handle.object sameHandle).trans (codeObject.trans endpoint)
    rcases product with received | ⟨empty, noProduct⟩
    · have encodedProduct := NativeCode.product_exact interpreted.product
      rw [received] at encodedProduct
      cases actualProduct : call.product <;> simp only [actualProduct, NativeCode.encodeProduct] at encodedProduct
      all_goals try contradiction
      next bytes =>
        have sameBytes : NativeCode.encodeBytes bytes = use.bytes := NativeCode.Product.received.inj encodedProduct
        rw [native_read_selected_caller journal use.position point selected call embedded _ _ _ bytes handle
          op actualProduct actualInput actualObject]
        exact sameBytes
    · have decoded := interpreted.product
      rw [noProduct] at decoded
      have actualProduct : call.product = .none := (Option.some.inj decoded).symm
      rw [native_read_selected_none journal use.position point selected call embedded actualProduct]
      exact empty.symm

end LeanCage.Host.PrivateStreams
