import GatewayChannelPairSource
import GatewayChannelCode

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {ticks : List (ActorTick runtime)}

-- §FS-host-boundary.ownership: Consume the source-produced pending pair data
-- on its SAME stored kernel row. The pair, freshness, endpoint/OFD orientation
-- and source lifetime are derived without SDK return or C copyout premises.
theorem actual_pending_source_pair_birth {ipc : ObjectId → Prop} (platform : SocketPairContract native ipc)
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    (use : ChannelCode.PairUse) (source : use.Consistent)
    (point : SelectedNativeCut process child native hostUid before after callers next ticks use.position)
    (selected : selectNativeCut journal use.position = some point)
    (call : NativeCallAt native point.tick point.cut.priorNative point.cut.nextNative)
    (embedded : embeddedNative point.cut.current = some call)
    (interpreted : NativeCode.Interprets use.row call) :
    ∃ pair, ∃ entry : PairBirthEntry process child native hostUid before after callers next ticks pair,
      ActualPairBirth journal entry ∧ entry.position = use.position ∧
      entry.call.token = use.invocation.key.process ∧
      pair.caller = use.leftObject ∧ pair.engine = use.rightObject ∧
      entry.firstHandle.description = use.leftDescription ∧ entry.secondHandle.description = use.rightDescription ∧
      ipc pair.caller ∧ ipc pair.engine := by
  obtain ⟨formed, process, order, operation, product, leftBound, rightBound, separateSlots,
    separateObjects, separateDescriptions, leftReference, rightReference, leftFlag, rightFlag⟩ := source
  have leftWidth : use.leftFd < 2 ^ 64 := by omega
  have rightWidth : use.rightFd < 2 ^ 64 := by omega
  obtain ⟨left, leftPresent, leftObject, leftDescription⟩ := leftReference
  obtain ⟨right, rightPresent, rightObject, rightDescription⟩ := rightReference
  have actualOperation : use.row.operation = NativeCode.encodeOperation (.socketPair 1 526337 0) := operation
  have actualProduct : use.row.product = NativeCode.encodeProduct
      (.socketPair (UInt64.ofNat use.leftFd) (UInt64.ofNat use.rightFd)) := by
    simpa only [NativeCode.encodeProduct, UInt64.toNat_ofNat_of_lt' leftWidth,
      UInt64.toNat_ofNat_of_lt' rightWidth] using product
  have decodedOperation := interpreted.operation
  rw [actualOperation, NativeCode.operation_roundtrip] at decodedOperation
  have decodedProduct := interpreted.product
  rw [actualProduct, NativeCode.product_roundtrip] at decodedProduct
  obtain ⟨pair, entry, actual, position, token, first, second, code, leftIpc, rightIpc, caller, engine⟩ :=
    actual_pair_birth platform journal point selected call embedded (UInt64.ofNat use.leftFd)
      (UInt64.ofNat use.rightFd) (Option.some.inj decodedOperation).symm (Option.some.inj decodedProduct).symm
  have output : entry.code.afterReferences = use.row.afterReferences := by
    rw [code, interpreted.output]
    rfl
  have firstInput := entry.firstInput
  rw [first] at firstInput
  have secondInput := entry.secondInput
  rw [second] at secondInput
  have firstCode : NativeCode.encodeHandle entry.firstHandle = left :=
    encoded_reference_handle entry.call.afterReferences (UInt64.ofNat use.leftFd) entry.firstHandle left firstInput
      (by rw [← entry.interpreted.output, output]; simpa only [UInt64.toNat_ofNat_of_lt' leftWidth] using leftPresent)
  have secondCode : NativeCode.encodeHandle entry.secondHandle = right :=
    encoded_reference_handle entry.call.afterReferences (UInt64.ofNat use.rightFd) entry.secondHandle right secondInput
      (by rw [← entry.interpreted.output, output]; simpa only [UInt64.toNat_ofNat_of_lt' rightWidth] using rightPresent)
  refine ⟨pair, entry, actual, position, token.trans (interpreted.process.symm.trans process), ?_, ?_, ?_, ?_, leftIpc, rightIpc⟩
  · exact caller.trans ((congrArg NativeCode.Handle.object firstCode).trans leftObject)
  · exact engine.trans ((congrArg NativeCode.Handle.object secondCode).trans rightObject)
  · exact (congrArg NativeCode.Handle.description firstCode).trans leftDescription
  · exact (congrArg NativeCode.Handle.description secondCode).trans rightDescription

end LeanCage.Host.PrivateStreams
