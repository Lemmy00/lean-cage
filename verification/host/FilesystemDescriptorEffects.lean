import FilesystemReferenceCustody

namespace LeanCage.Host.Kernel
open Filesystem

-- §AR-host-boundary.primitives: A real close or closedir may retire its FD on error or
-- lost acknowledgement. Neither one operation introduces or retargets a raw FD reference.
structure DescriptorRetirementContract (kernel : Contract) : Prop where
  backward : ∀ before after request observed fd handle,
    kernel.step before request observed after → (request.op = .close ∨ request.op = .dirClose) →
    after.handles fd = some handle → before.handles fd = some handle

-- §FS-host-boundary.ownership: This is a single selected raw call, with its exact optional
-- reply. Other engines retain their own tables; no helper or global FD frame is assumed.
theorem filesystem_reference_subset {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {tick : ActorTick runtime} {actor : ActorId}
    {request : Request} {observed : Option Reply}
    (selected : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (backward : ∀ before after, kernel.step before request observed after →
      ∀ fd handle, after.handles fd = some handle → before.handles fd = some handle) :
    EngineReferencesFrom tick.before tick.after := by
  rcases tick with ⟨action, before, after, operation⟩
  cases operation with
  | launch => cases selected
  | @returned β population owner current effect next reply world present alive head actual =>
    dsimp only [ActorAction.eventFor] at selected
    split at selected
    · rename_i sameActor
      subst owner
      cases observed <;> cases selected
      intro query later afterPresent fd handle live
      by_cases sameQuery : query = actor
      · subst query
        simp only [Population.advance, Population.install, ite_eq_left] at afterPresent
        have same := Option.some.inj afterPresent
        subst later
        exact ⟨current, present, backward _ _ actual fd handle live⟩
      · exact ⟨later, by
          simpa only [Population.advance, Population.install, ite_eq_right sameQuery] using afterPresent, live⟩
    · cases selected
  | @lost β population owner current effect next world present alive head actual =>
    dsimp only [ActorAction.eventFor] at selected
    split at selected
    · rename_i sameActor
      subst owner
      cases observed <;> cases selected
      intro query later afterPresent fd handle live
      by_cases sameQuery : query = actor
      · subst query
        simp only [Population.advance, Population.install, ite_eq_left] at afterPresent
        have same := Option.some.inj afterPresent
        subst later
        exact ⟨current, present, backward _ _ actual fd handle live⟩
      · exact ⟨later, by
          simpa only [Population.advance, Population.install, ite_eq_right sameQuery] using afterPresent, live⟩
    · cases selected
  | foreign | retire | nativeRetire => cases selected

theorem closed_filesystem_references_owned {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} (retirement : DescriptorRetirementContract kernel)
    {ticks : List (ActorTick runtime)} {tick : ActorTick runtime} {actor : ActorId}
    {request : Request} {observed : Option Reply}
    (selected : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (closing : request.op = .close ∨ request.op = .dirClose) (consistent : tick.before.Consistent)
    {first final : Family} {oldCatalogue newCatalogue : Catalogue runtime ticks}
    (labels : ExistingLabels tick.before.shared tick.after.shared first final)
    (included : ∀ record ∈ oldCatalogue, record ∈ newCatalogue)
    (owned : EngineReferencesOwned runtime ticks tick.before first oldCatalogue) :
    EngineReferencesOwned runtime ticks tick.after final newCatalogue :=
  retained_engine_references_owned consistent
    (filesystem_reference_subset selected (fun _ _ actual fd handle live =>
      retirement.backward _ _ _ _ fd handle actual closing live)) labels included owned

end LeanCage.Host.Kernel
