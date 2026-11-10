import FilesystemOpenTargets

namespace LeanCage.Host.Kernel
open Filesystem

variable {sourceProgram : Program UInt32}

-- §FS-host-boundary.ownership: This one-row adapter preserves exact old references
-- and classifies only genuinely introduced handles. It has no helper-frame premise.
theorem filesystem_references_owned_of_introductions {kernel : Contract}
    {runtime : ActorRuntime kernel sourceProgram} {ticks : List (ActorTick runtime)}
    {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply}
    (selected : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    {family : Family} {catalogue : Catalogue runtime ticks}
    (owned : EngineReferencesOwned runtime ticks tick.before family catalogue)
    (origins : ∀ fd handle, tick.after.shared.handles fd = some handle →
      engine.references fd = some handle ∨
        ∀ scope, family handle.object = some scope → catalogue.Owns actor scope) :
    EngineReferencesOwned runtime ticks tick.after family catalogue := by
  rcases tick with ⟨action, before, after, operation⟩
  cases operation with
  | launch => cases selected
  | @returned β population owner current effect next reply world ownerPresent alive head actual =>
    dsimp only [ActorAction.eventFor] at selected
    split at selected
    · rename_i sameActor
      subst owner
      have sameEngine := Option.some.inj (present.symm.trans ownerPresent)
      subst engine
      cases observed <;> cases selected
      intro query later afterPresent fd handle scope live privateObject
      by_cases sameQuery : query = actor
      · subst query
        simp only [Population.advance, Population.install, ite_eq_left] at afterPresent
        have same := Option.some.inj afterPresent
        subst later
        rcases origins fd handle live with old | introduced
        · exact owned actor current ownerPresent fd handle scope old privateObject
        · exact introduced scope privateObject
      · exact owned query later (by
          simpa only [Population.advance, Population.install, ite_eq_right sameQuery] using afterPresent)
          fd handle scope live privateObject
    · cases selected
  | @lost β population owner current effect next world ownerPresent alive head actual =>
    dsimp only [ActorAction.eventFor] at selected
    split at selected
    · rename_i sameActor
      subst owner
      have sameEngine := Option.some.inj (present.symm.trans ownerPresent)
      subst engine
      cases observed <;> cases selected
      intro query later afterPresent fd handle scope live privateObject
      by_cases sameQuery : query = actor
      · subst query
        simp only [Population.advance, Population.install, ite_eq_left] at afterPresent
        have same := Option.some.inj afterPresent
        subst later
        rcases origins fd handle live with old | introduced
        · exact owned actor current ownerPresent fd handle scope old privateObject
        · exact introduced scope privateObject
      · exact owned query later (by
          simpa only [Population.advance, Population.install, ite_eq_right sameQuery] using afterPresent)
          fd handle scope live privateObject
    · cases selected
  | foreign | retire | nativeRetire => cases selected

theorem filesystem_references_owned_of_origins {kernel : Contract}
    {runtime : ActorRuntime kernel sourceProgram} {ticks : List (ActorTick runtime)}
    {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply}
    (selected : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    {family : Family} {catalogue : Catalogue runtime ticks}
    (owned : EngineReferencesOwned runtime ticks tick.before family catalogue)
    (origins : ∀ fd handle, tick.after.shared.handles fd = some handle →
      engine.references fd = some handle ∨ family handle.object = none) :
    EngineReferencesOwned runtime ticks tick.after family catalogue := by
  apply filesystem_references_owned_of_introductions selected present owned
  intro fd handle live
  rcases origins fd handle live with old | publicObject
  · exact .inl old
  · right
    intro scope label
    rw [publicObject] at label
    cases label

end LeanCage.Host.Kernel
