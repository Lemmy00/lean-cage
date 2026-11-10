import GatewayChannelBirths
import FilesystemReferenceLifetime

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

-- §AR-host-boundary.primitives: Each selected native call observes its actual
-- live FD/OFD tables. This states no invocation role, queue or reader authority.
structure NativeDescriptionContract {kernel : Contract} (native : NativePrimitive kernel) : Prop where
  before_references : ∀ {program : Program UInt32} {runtime : ActorRuntime kernel program}
    {tick : ActorTick runtime} {before after : NativeProcesses} (call : NativeCallAt native tick before after),
    ValidReferences tick.before.shared call.beforeReferences.handles
  after_references : ∀ {program : Program UInt32} {runtime : ActorRuntime kernel program}
    {tick : ActorTick runtime} {before after : NativeProcesses} (call : NativeCallAt native tick before after),
    ValidReferences tick.after.shared call.afterReferences.handles

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {ticks : List (ActorTick runtime)} {pair : Pair}

def PairBirthEntry.endpointHandle
    (entry : PairBirthEntry process child native hostUid before after callers next ticks pair) : Side → Handle
  | .caller => entry.firstHandle
  | .engine => entry.secondHandle

theorem pair_birth_endpoint_object
    (entry : PairBirthEntry process child native hostUid before after callers next ticks pair) (side : Side) :
    (entry.endpointHandle side).object = pair.endpoint side := by
  cases side
  · exact entry.callerObject
  · exact entry.engineObject

-- §FS-host-boundary.ownership: Allocation of the socket OFD follows from the
-- SAME call's actual copyout handles, including committed creation without ACK.
theorem pair_birth_description_allocated (descriptions : NativeDescriptionContract native)
    (entry : PairBirthEntry process child native hostUid before after callers next ticks pair) (side : Side) :
    entry.tick.after.shared.descriptionAllocated (entry.endpointHandle side).description = true := by
  cases side with
  | caller => exact (descriptions.after_references entry.call entry.first entry.firstHandle entry.firstInput).2.1
  | engine => exact (descriptions.after_references entry.call entry.second entry.secondHandle entry.secondInput).2.1

theorem actor_journal_description_allocated {program : Program UInt32}
    {actualRuntime : ActorRuntime kernel program} (references : ReferenceContract actualRuntime)
    {initial final : Population} {all : List (ActorTick actualRuntime)}
    (journal : ActorJournal actualRuntime initial all final) (description : DescriptionId)
    (allocated : initial.shared.descriptionAllocated description = true) :
    final.shared.descriptionAllocated description = true := by
  induction journal with
  | nil => exact allocated
  | @cons tick rest final tail ih =>
    exact ih (actor_step_description_allocated references tick.operation description allocated)

theorem selected_description_before (references : ReferenceContract runtime)
    {initial final : Population} (journal : ActorJournal runtime initial ticks final)
    {first last : Nat} {earlier later : ActorTick runtime}
    (ordered : first < last) (atFirst : ticks[first]? = some earlier) (atLast : ticks[last]? = some later)
    (description : DescriptionId) (allocated : earlier.after.shared.descriptionAllocated description = true) :
    later.before.shared.descriptionAllocated description = true := by
  induction first generalizing ticks initial last with
  | zero =>
    cases journal with
    | nil => cases atFirst
    | @cons tick rest final tail =>
      have same := Option.some.inj atFirst
      subst earlier
      cases last with
      | zero => omega
      | succ last =>
        obtain ⟨leading, preceding⟩ := journal_to_selected tail atLast
        exact actor_journal_description_allocated references preceding description allocated
  | succ first ih =>
    cases last with
    | zero => omega
    | succ last =>
      cases journal with
      | nil => cases atFirst
      | cons tail => exact ih tail (by omega) atFirst atLast

end LeanCage.Host.PrivateStreams
