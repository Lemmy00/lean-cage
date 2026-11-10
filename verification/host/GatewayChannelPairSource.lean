import GatewayChannelPair

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

theorem encoded_reference_handle (references : NativeReferences) (fd : UInt64)
    (handle : Handle) (code : NativeCode.Handle)
    (input : references.handles fd = some handle)
    (output : (NativeCode.encodeReferences references).handles fd.toNat = some code) :
    NativeCode.encodeHandle handle = code := by
  simpa only [NativeCode.encodeReferences, UInt64.toNat_lt, ↓reduceIte,
    UInt64.ofNat_toNat, input, Option.map_some, Option.some.injEq] using output

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {ticks : List (ActorTick runtime)}

-- §AR-host-boundary.interfaces.gateway: The source-produced copyout words
-- and output leases bind the actual fresh kernel pair in the same orientation.
theorem actual_source_pair_birth {ipc : ObjectId → Prop} (platform : SocketPairContract native ipc)
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    {position : Nat}
    (selected : SelectedNativeCut process child native hostUid before after callers next ticks position)
    (actual : selectNativeCut journal position = some selected)
    (call : NativeCallAt native selected.tick selected.cut.priorNative selected.cut.nextNative)
    (embedded : embeddedNative selected.cut.current = some call)
    (code : NativeCode.CallRow) (interpreted : NativeCode.Interprets code call)
    (first second : UInt64)
    (operands : code.operation = NativeCode.encodeOperation (.socketPair 1 526337 0))
    (committed : code.product = NativeCode.encodeProduct (.socketPair first second))
    (left right : NativeCode.Handle)
    (firstOutput : code.afterReferences.handles first.toNat = some left)
    (secondOutput : code.afterReferences.handles second.toNat = some right) :
    ∃ pair, ∃ entry : PairBirthEntry process child native hostUid before after callers next ticks pair,
      ActualPairBirth journal entry ∧ entry.position = position ∧ entry.first = first ∧ entry.second = second ∧
      pair.caller = left.object ∧ pair.engine = right.object ∧
      entry.firstHandle.description = left.description ∧ entry.secondHandle.description = right.description ∧
      ipc pair.caller ∧ ipc pair.engine := by
  have operation := interpreted.operation
  rw [operands, NativeCode.operation_roundtrip] at operation
  have creation := interpreted.product
  rw [committed, NativeCode.product_roundtrip] at creation
  obtain ⟨pair, entry, actual, position, _, firstFd, secondFd, entryCode, leftIpc, rightIpc, _, _⟩ :=
    actual_pair_birth platform journal selected actual call embedded first second
      (Option.some.inj operation).symm (Option.some.inj creation).symm
  have sameOutput : entry.code.afterReferences = code.afterReferences := by
    rw [entryCode, interpreted.output]
    rfl
  have firstInput := entry.firstInput
  rw [firstFd] at firstInput
  have secondInput := entry.secondInput
  rw [secondFd] at secondInput
  have firstCode : NativeCode.encodeHandle entry.firstHandle = left :=
    encoded_reference_handle entry.call.afterReferences first entry.firstHandle left firstInput
      (by rw [← entry.interpreted.output, sameOutput]; exact firstOutput)
  have secondCode : NativeCode.encodeHandle entry.secondHandle = right :=
    encoded_reference_handle entry.call.afterReferences second entry.secondHandle right secondInput
      (by rw [← entry.interpreted.output, sameOutput]; exact secondOutput)
  refine ⟨pair, entry, actual, position, firstFd, secondFd, ?_, ?_, ?_, ?_, leftIpc, rightIpc⟩
  · exact entry.callerObject.symm.trans (congrArg NativeCode.Handle.object firstCode)
  · exact entry.engineObject.symm.trans (congrArg NativeCode.Handle.object secondCode)
  · exact congrArg NativeCode.Handle.description firstCode
  · exact congrArg NativeCode.Handle.description secondCode

end LeanCage.Host.PrivateStreams
