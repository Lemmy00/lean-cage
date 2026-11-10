import FilesystemRootCatalogue

namespace LeanCage.Host.Kernel
open Filesystem

variable {sourceProgram : Program UInt32}

-- §FS-host-boundary.ownership: Custody is tied to the actual engine table and the recorded
-- lifetime birth owner, including unbound roots whose names were retired after an error.
def EngineReferencesOwned {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram)
    (ticks : List (ActorTick runtime)) (population : Population) (family : Family)
    (catalogue : Catalogue runtime ticks) : Prop :=
  ∀ actor engine, population.actors actor = some engine → ∀ fd handle scope,
    engine.references fd = some handle → family handle.object = some scope → catalogue.Owns actor scope

def RetainingAction : ActorAction → Prop
  | .returned _ (.filesystem request) _ | .lost _ (.filesystem request) => RetainsDescriptors request.op
  | _ => False

def EngineReferencesFrom (before after : Population) : Prop :=
  ∀ actor engine, after.actors actor = some engine → ∀ fd handle, engine.references fd = some handle →
    ∃ prior, before.actors actor = some prior ∧ prior.references fd = some handle

private def filesystemOp : Program.Event → Option Op
  | .returned (.filesystem request) _ | .lost (.filesystem request) => some request.op
  | _ => none

theorem retaining_action_of_filesystem_event {action : ActorAction} {actor : ActorId}
    {request : Request} {observed : Option Reply}
    (selected : action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (retaining : RetainsDescriptors request.op) : RetainingAction action := by
  have tagged := congrArg (fun value => value.bind filesystemOp) selected
  cases action with
  | launch | foreign | retire | nativeRetire => cases selected
  | returned owner effect reply =>
    by_cases sameActor : actor = owner
    · subst actor
      cases effect with
      | filesystem actualRequest =>
        have same : actualRequest.op = request.op := by
          cases observed <;> simpa [ActorAction.eventFor, Program.filesystemPrefixEvent, filesystemOp] using tagged
        simpa only [RetainingAction, same] using retaining
      | spawn | read | wait | terminate | tryWait | descriptor =>
        cases observed <;> simp [ActorAction.eventFor, Program.filesystemPrefixEvent, filesystemOp] at tagged
    · cases observed <;> simp [ActorAction.eventFor, sameActor, Program.filesystemPrefixEvent, filesystemOp] at tagged
  | lost owner effect =>
    by_cases sameActor : actor = owner
    · subst actor
      cases effect with
      | filesystem actualRequest =>
        have same : actualRequest.op = request.op := by
          cases observed <;> simpa [ActorAction.eventFor, Program.filesystemPrefixEvent, filesystemOp] using tagged
        simpa only [RetainingAction, same] using retaining
      | spawn | read | wait | terminate | tryWait | descriptor =>
        cases observed <;> simp [ActorAction.eventFor, Program.filesystemPrefixEvent, filesystemOp] at tagged
    · cases observed <;> simp [ActorAction.eventFor, sameActor, Program.filesystemPrefixEvent, filesystemOp] at tagged

-- §FS-host-boundary.ownership: Every retained raw reference comes from the SAME actor before
-- this one real filesystem call. Returned and lost calls use the same descriptor/OFD law.
theorem retained_action_references {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (descriptors : DescriptorContract kernel) {action : ActorAction} {before after : Population}
    (step : ActorStep runtime action before after) (retaining : RetainingAction action) :
    EngineReferencesFrom before after := by
  cases step with
  | launch => cases retaining
  | @returned β population owner current effect next reply world present alive head actual =>
    cases effect with
    | filesystem request =>
      intro actor engine afterPresent fd handle live
      by_cases sameActor : actor = owner
      · subst actor
        have sameEngine : current.returned (.filesystem request) reply next world = engine := by
          apply Option.some.inj
          simpa only [Population.advance, Population.install, ite_eq_left] using afterPresent
        subst engine
        have old : current.references fd = some handle := by
          change world.handles fd = some handle at live
          rw [descriptors.retained _ _ _ _ actual retaining] at live
          exact live
        exact ⟨current, present, old⟩
      · exact ⟨engine, by
          simpa only [Population.advance, Population.install, ite_eq_right sameActor] using afterPresent, live⟩
    | spawn | read | wait | terminate | tryWait | descriptor => cases retaining
  | @lost β population owner current effect next world present alive head actual =>
    cases effect with
    | filesystem request =>
      intro actor engine afterPresent fd handle live
      by_cases sameActor : actor = owner
      · subst actor
        have sameEngine : current.lost (.filesystem request) world = engine := by
          apply Option.some.inj
          simpa only [Population.advance, Population.install, ite_eq_left] using afterPresent
        subst engine
        have old : current.references fd = some handle := by
          change world.handles fd = some handle at live
          rw [descriptors.retained _ _ _ _ actual retaining] at live
          exact live
        exact ⟨current, present, old⟩
      · exact ⟨engine, by
          simpa only [Population.advance, Population.install, ite_eq_right sameActor] using afterPresent, live⟩
    | spawn | read | wait | terminate | tryWait | descriptor => cases retaining
  | foreign | retire | nativeRetire => cases retaining

theorem Catalogue.Owns.weaken {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {ticks : List (ActorTick runtime)} {before after : Catalogue runtime ticks}
    (included : ∀ record ∈ before, record ∈ after) {actor : ActorId} {object : ObjectId}
    (owned : before.Owns actor object) : after.Owns actor object := by
  obtain ⟨record, member, owner, identity⟩ := owned
  exact ⟨record, included record member, owner, identity⟩

theorem empty_engine_references_owned {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram)
    (ticks : List (ActorTick runtime)) (world : World) (family : Family) (catalogue : Catalogue runtime ticks) :
    EngineReferencesOwned runtime ticks (Population.empty world) family catalogue := by
  intro actor engine impossible
  cases impossible

-- §FS-host-boundary.ownership: A fresh root label cannot claim a peer's pre-existing raw FD.
-- Scope publication may only release an old label; its catalogue owner never transfers.
theorem retained_engine_references_owned {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {ticks : List (ActorTick runtime)} {before after : Population} {first final : Family}
    {oldCatalogue newCatalogue : Catalogue runtime ticks}
    (consistent : before.Consistent) (references : EngineReferencesFrom before after)
    (labels : ExistingLabels before.shared after.shared first final)
    (included : ∀ record ∈ oldCatalogue, record ∈ newCatalogue)
    (owned : EngineReferencesOwned runtime ticks before first oldCatalogue) :
    EngineReferencesOwned runtime ticks after final newCatalogue := by
  intro actor engine present fd handle scope live privateObject
  obtain ⟨prior, beforePresent, beforeLive⟩ := references actor engine present fd handle live
  have allocated := (consistent actor prior beforePresent fd handle beforeLive).1
  have oldLabel : first handle.object = some scope := by
    rcases labels handle.object allocated with same | released
    · exact same.symm.trans privateObject
    · rw [privateObject] at released
      cases released
  exact (owned actor prior beforePresent fd handle scope beforeLive oldLabel).weaken included

-- §FS-host-boundary.ownership: This consumer derives reference retention from the actual
-- selected source call, including a lost reply; no all-engine reference frame is supplied.
theorem retained_filesystem_references_owned {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (descriptors : DescriptorContract kernel) {ticks : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {request : Request} {observed : Option Reply}
    (selected : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (retaining : RetainsDescriptors request.op) (consistent : tick.before.Consistent)
    {first final : Family} {oldCatalogue newCatalogue : Catalogue runtime ticks}
    (labels : ExistingLabels tick.before.shared tick.after.shared first final)
    (included : ∀ record ∈ oldCatalogue, record ∈ newCatalogue)
    (owned : EngineReferencesOwned runtime ticks tick.before first oldCatalogue) :
    EngineReferencesOwned runtime ticks tick.after final newCatalogue :=
  retained_engine_references_owned consistent
    (retained_action_references descriptors tick.operation (retaining_action_of_filesystem_event selected retaining))
    labels included owned

end LeanCage.Host.Kernel
