import FilesystemChannelWrites
import FilesystemPrimitiveRoles
import FilesystemDescriptorEffects

namespace LeanCage.Host.Kernel
open Filesystem

-- §AR-host-boundary.primitives: Each allocation introduces a real fresh OFD lifetime.
-- An O_PATH or pathname inode view is not equated with an inherited I/O description.
structure DescriptionIntroductionContract (kernel : Contract) : Prop where
  opened : ∀ before after request observed fd handle,
    kernel.step before request observed after → request.op = .openAt → ClosedOpenRequest request →
    after.handles fd = some handle → before.handles fd = some handle ∨ before.descriptionAllocated handle.description = false
  socket : ∀ before after request observed fd handle,
    kernel.step before request observed after → request.op = .socket → after.handles fd = some handle →
    before.handles fd = some handle ∨ before.descriptionAllocated handle.description = false
  executable : ∀ before after request observed fd handle,
    kernel.step before request observed after → request.op = .selfExecutable → after.handles fd = some handle →
    before.handles fd = some handle ∨ before.descriptionAllocated handle.description = false

theorem operation_old_description_backward {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram}
    (descriptors : DescriptorContract kernel) (introductions : DescriptionIntroductionContract kernel)
    (retirement : DescriptorRetirementContract kernel) (sdk : RuntimeDescriptorContract runtime)
    {β : Type} {actor : ActorId} {effect : Effect β} {observed : Option β} {before after : World}
    (actual : ActorOperation runtime actor effect observed before after) (closed : ClosedEffect effect)
    {fd : UInt64} {handle : Handle} (old : before.descriptionAllocated handle.description = true)
    (live : after.handles fd = some handle) : before.handles fd = some handle := by
  cases effect with
  | filesystem request =>
    by_cases opening : request.op = .openAt
    · rcases introductions.opened _ _ _ _ _ _ actual opening closed live with reference | fresh
      · exact reference
      · rw [old] at fresh; cases fresh
    · by_cases socket : request.op = .socket
      · rcases introductions.socket _ _ _ _ _ _ actual socket live with reference | fresh
        · exact reference
        · rw [old] at fresh; cases fresh
      · by_cases executable : request.op = .selfExecutable
        · rcases introductions.executable _ _ _ _ _ _ actual executable live with reference | fresh
          · exact reference
          · rw [old] at fresh; cases fresh
        · by_cases closing : request.op = .close ∨ request.op = .dirClose
          · exact retirement.backward _ _ _ _ _ _ actual closing live
          · have retained : RetainsDescriptors request.op :=
              ⟨opening, socket, executable, fun same => closing (.inl same), fun same => closing (.inr same)⟩
            rw [descriptors.retained _ _ _ _ actual retained] at live
            exact live
  | spawn | read | wait | terminate | tryWait | descriptor => exact sdk.new_reference _ _ _ _ _ _ _ actual live

-- §FS-host-boundary.caller: The supported open operands come from the SAME source row.
-- This is not an initialized-safe role supplied for an arbitrary syscall transcript.
theorem source_return_closed_effect {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {actor : ActorId} {ordinal : Nat} {β : Type} {effect : Effect β} {reply : β} {before after : World}
    (sampled : SourceReturnAt runtime all actor ordinal β effect reply before after) : ClosedEffect effect := by
  cases effect with
  | filesystem request =>
    obtain ⟨position, tick, first, last, selected, action, present, afterPresent, count, beforeWorld, afterWorld⟩ := sampled
    apply primitive_closed_open (observed := some reply)
    apply selected_source_prefix_for journal selected (engine := first) (actor := actor)
    · simp only [action, ActorAction.eventFor, ↓reduceIte, Program.filesystemPrefixEvent]
    · exact present
  | spawn | read | wait | terminate | tryWait | descriptor => exact True.intro

-- §FS-host-boundary.ownership: A current SAME-OFD reference existed at this earlier source
-- boundary. Individual allocation/close/SDK laws retain reuse, aliases and lost-effect cases.
theorem actor_history_old_description_backward {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram}
    (descriptors : DescriptorContract kernel) (introductions : DescriptionIntroductionContract kernel)
    (retirement : DescriptorRetirementContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (references : ReferenceContract runtime)
    {actor : ActorId} {origin : OperationOrigin} {ordinal : Nat} {before after : World} {events : List Program.Event}
    (history : ActorHistoryWith runtime actor origin ordinal before events after)
    (closed : ∀ ordinal β (effect : Effect β) reply before after,
      origin ordinal β effect reply before after → ClosedEffect effect)
    {fd : UInt64} {handle : Handle} (old : before.descriptionAllocated handle.description = true)
    (live : after.handles fd = some handle) : before.handles fd = some handle := by
  induction history with
  | nil => exact live
  | environment actual tail ih =>
    have current := ih (kernel.interference_description_allocation _ _ _ actual old) live
    rw [kernel.interference_handles _ _ actual] at current
    exact current
  | returned actual sampled tail ih =>
    have current := ih (operation_description_allocated references actual _ old) live
    exact operation_old_description_backward descriptors introductions retirement sdk actual
      (closed _ _ _ _ _ _ sampled) old current

end LeanCage.Host.Kernel
