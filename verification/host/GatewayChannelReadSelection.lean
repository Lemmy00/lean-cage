import GatewayChannelReadJournal

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {ticks : List (ActorTick runtime)} {pair : Pair}

-- §AR-host-boundary.interfaces.gateway: The canonical entry selects this
-- exact stored operation, including its actual input handle and bytes.
theorem native_read_selected_caller
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    (position : Nat)
    (point : SelectedNativeCut process child native hostUid before after callers next ticks position)
    (selected : selectNativeCut journal position = some point)
    (call : NativeCallAt native point.tick point.cut.priorNative point.cut.nextNative)
    (embedded : embeddedNative point.cut.current = some call)
    (descriptor extent flags : UInt64) (bytes : ByteArray) (handle : Handle)
    (operation : call.operation = .receive descriptor extent flags) (product : call.product = .received bytes)
    (input : call.beforeReferences.handles descriptor = some handle) (endpoint : handle.object = pair.caller) :
    nativeCallerBytesAt (pair := pair) journal position = bytes.data.toList := by
  classical
  let entry : NativeReadEntry process child native hostUid before after callers next ticks pair := {
    position, tick := point.tick, cut := point.cut, call, embedded, code := NativeCode.encodeCall call,
    interpreted := NativeCode.encode_call_exact call, descriptor, extent, flags, bytes,
    operation, product, receiver := .caller, handle, input, endpoint }
  have chosen : nativeReadAt journal position = some entry := by
    unfold nativeReadAt
    split
    next missing => rw [selected] at missing; cases missing
    next chosen atPoint =>
      have identity := Option.some.inj (atPoint.symm.trans selected)
      subst chosen
      split
      next missing => rw [embedded] at missing; cases missing
      next actual atCall =>
        have identity := Option.some.inj (atCall.symm.trans embedded)
        subst actual
        split
        next actualDescriptor actualExtent actualFlags atOperation =>
          have identity := NativeOperation.receive.inj (atOperation.symm.trans operation)
          obtain ⟨rfl, rfl, rfl⟩ := identity
          split
          next actualBytes atProduct =>
            have identity := NativeProduct.received.inj (atProduct.symm.trans product)
            subst actualBytes
            split
            next missing => rw [input] at missing; cases missing
            next actualHandle atInput =>
              have identity := Option.some.inj (atInput.symm.trans input)
              subst actualHandle
              simp only [endpoint, ↓reduceDIte]
              rfl
          next noProduct => exact False.elim (noProduct bytes product)
        next noOperation => exact False.elim (noOperation descriptor extent flags operation)
  simp only [nativeCallerBytesAt, chosen, entry, ↓reduceIte]

theorem native_read_selected_none
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    (position : Nat)
    (point : SelectedNativeCut process child native hostUid before after callers next ticks position)
    (selected : selectNativeCut journal position = some point)
    (call : NativeCallAt native point.tick point.cut.priorNative point.cut.nextNative)
    (embedded : embeddedNative point.cut.current = some call) (product : call.product = .none) :
    nativeCallerBytesAt (pair := pair) journal position = [] := by
  classical
  have chosen : nativeReadAt (pair := pair) journal position = none := by
    unfold nativeReadAt
    split
    next missing => rfl
    next chosen atPoint =>
      have identity := Option.some.inj (atPoint.symm.trans selected)
      subst chosen
      split
      next missing => rfl
      next actual atCall =>
        have identity := Option.some.inj (atCall.symm.trans embedded)
        subst actual
        split
        next actualDescriptor actualExtent actualFlags atOperation =>
          split
          next bytes atProduct => rw [product] at atProduct; cases atProduct
          next noProduct => rfl
        next noOperation => rfl
  simp only [nativeCallerBytesAt, chosen]

end LeanCage.Host.PrivateStreams
