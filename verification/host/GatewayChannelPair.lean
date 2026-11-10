import GatewayChannelBirths
import FilesystemNativeCodeRows

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

-- §AR-host-boundary.primitives: These are only the effects of one actual
-- AF_UNIX socketpair, including a creation whose SDK reply is never observed.
structure PairAllocation {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {native : NativePrimitive kernel} {tick : ActorTick runtime} {before after : NativeProcesses}
    (ipc : ObjectId → Prop) (call : NativeCallAt native tick before after) (first second : UInt64) where
  left : Handle
  right : Handle
  leftOutput : call.afterReferences.handles first = some left
  rightOutput : call.afterReferences.handles second = some right
  leftBound : first.toNat ≤ 2147483647
  rightBound : second.toNat ≤ 2147483647
  leftInputEmpty : call.beforeReferences.handles first = none
  rightInputEmpty : call.beforeReferences.handles second = none
  otherOutputs : ∀ fd, fd ≠ first → fd ≠ second →
    call.afterReferences.handles fd = call.beforeReferences.handles fd
  otherCloseExec : ∀ fd, fd ≠ first → fd ≠ second →
    call.afterReferences.closeOnExec fd = call.beforeReferences.closeOnExec fd
  slotsSeparate : first ≠ second
  objectsSeparate : left.object ≠ right.object
  descriptionsSeparate : left.description ≠ right.description
  leftFresh : tick.before.shared.allocated left.object = false
  rightFresh : tick.before.shared.allocated right.object = false
  leftDescriptionFresh : tick.before.shared.descriptionAllocated left.description = false
  rightDescriptionFresh : tick.before.shared.descriptionAllocated right.description = false
  leftIpc : ipc left.object
  rightIpc : ipc right.object
  leftCloseExec : call.afterReferences.closeOnExec first = true
  rightCloseExec : call.afterReferences.closeOnExec second = true

structure SocketPairContract {kernel : Contract} (native : NativePrimitive kernel) (ipc : ObjectId → Prop) : Prop where
  created : ∀ {runtime : PrimitiveActorRuntime kernel} {tick : ActorTick runtime}
    {before after : NativeProcesses} (call : NativeCallAt native tick before after) first second,
    call.operation = .socketPair 1 526337 0 → call.product = .socketPair first second →
    Nonempty (PairAllocation ipc call first second)

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {ticks : List (ActorTick runtime)}

-- §FS-host-boundary.ownership: This producer chooses the pair from the
-- actual selected call's output handles, rather than accepting private IDs.
theorem actual_pair_birth {ipc : ObjectId → Prop} (platform : SocketPairContract native ipc)
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    {position : Nat}
    (selected : SelectedNativeCut process child native hostUid before after callers next ticks position)
    (actual : selectNativeCut journal position = some selected)
    (call : NativeCallAt native selected.tick selected.cut.priorNative selected.cut.nextNative)
    (embedded : embeddedNative selected.cut.current = some call)
    (first second : UInt64) (operation : call.operation = .socketPair 1 526337 0)
    (product : call.product = .socketPair first second) :
    ∃ pair, ∃ entry : PairBirthEntry process child native hostUid before after callers next ticks pair,
      ActualPairBirth journal entry ∧ entry.position = position ∧ entry.call.token = call.token ∧
      entry.first = first ∧ entry.second = second ∧ entry.code = NativeCode.encodeCall call ∧
      ipc pair.caller ∧ ipc pair.engine ∧
      pair.caller = (entry.firstHandle).object ∧ pair.engine = (entry.secondHandle).object := by
  obtain ⟨allocation⟩ := platform.created call first second operation product
  let pair : Pair := ⟨allocation.left.object, allocation.right.object, allocation.objectsSeparate⟩
  let entry : PairBirthEntry process child native hostUid before after callers next ticks pair := {
    position
    tick := selected.tick
    cut := selected.cut
    call
    embedded
    code := NativeCode.encodeCall call
    interpreted := NativeCode.encode_call_exact call
    first
    second
    operation
    product
    firstHandle := allocation.left
    secondHandle := allocation.right
    firstInput := allocation.leftOutput
    secondInput := allocation.rightOutput
    callerObject := rfl
    engineObject := rfl
    callerFresh := allocation.leftFresh
    engineFresh := allocation.rightFresh }
  refine ⟨pair, entry, ?_, rfl, rfl, rfl, rfl, rfl, allocation.leftIpc, allocation.rightIpc, rfl, rfl⟩
  change selectNativeCut journal position = some ⟨selected.tick, selected.cut⟩
  exact actual

end LeanCage.Host.PrivateStreams
