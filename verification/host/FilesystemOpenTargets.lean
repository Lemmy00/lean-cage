import FilesystemLookupNames
import FilesystemReferenceCustody

namespace LeanCage.Host.Kernel
open Filesystem

-- §AR-host-boundary.primitives: This is the target of one actual raw open, indexed by the
-- same optional acknowledgement. It is not an invented successful reply or helper transcript.
structure OpenTargetContract (kernel : Contract) (semantics : NameSemanticsView)
    (initialObjects : ObjectId → Bool) (dataObjects : ObjectId → Prop) where
  target : World → Request → Option Reply → World → ObjectId → Prop
  introduced : ∀ before after request observed fd handle,
    kernel.step before request observed after → request.op = .openAt → after.handles fd = some handle →
    before.handles fd = some handle ∨ (before.handles fd = none ∧ target before request observed after handle.object)
  single : ∀ before after request observed first second left right,
    kernel.step before request observed after → request.op = .openAt →
    before.handles first = none → before.handles second = none →
    after.handles first = some left → after.handles second = some right → first = second
  dot : ∀ before after request observed object parent,
    kernel.step before request observed after → target before request observed after object →
    request.op = .openAt → (request.second = directoryFlags ∨ request.second = readFlags) →
    before.handles request.first = some parent →
    request.left = ".".toUTF8 → object = parent.object
  child : ∀ before after request observed object parent,
    kernel.step before request observed after → target before request observed after object →
    request.op = .openAt → (request.second = directoryFlags ∨ request.second = readFlags) →
    before.handles request.first = some parent → Directories.component request.left = true →
    request.left ≠ ".".toUTF8 → request.left ≠ "..".toUTF8 → dataObjects object →
    (∃ storedName, before.entries parent.object storedName = some object ∧
      ((semantics.at before parent.object).byteExact → storedName = request.left)) ∨ initialObjects object = true
  young_child : ∀ before after request observed object parent,
    kernel.step before request observed after → target before request observed after object →
    request.op = .openAt → (request.second = directoryFlags ∨ request.second = readFlags) →
    before.handles request.first = some parent → Directories.component request.left = true →
    request.left ≠ ".".toUTF8 → request.left ≠ "..".toUTF8 →
    initialObjects parent.object = false → dataObjects parent.object →
    ∃ storedName, before.entries parent.object storedName = some object ∧
      ((semantics.at before parent.object).byteExact → storedName = request.left)
  parent : ∀ before after request observed object current,
    kernel.step before request observed after → target before request observed after object →
    request.op = .openAt → (request.second = directoryFlags ∨ request.second = readFlags) →
    before.handles request.first = some current →
    request.left = "..".toUTF8 → dataObjects object →
    object = current.object ∨ initialObjects object = true ∨ ∃ name, before.entries object name = some current.object
  root : ∀ before after request observed object,
    kernel.step before request observed after → target before request observed after object →
    request.op = .openAt → request.second = directoryFlags → request.first = cwd → request.left = "/".toUTF8 →
    initialObjects object = true
  cwd : ∀ before after request observed object,
    kernel.step before request observed after → target before request observed after object →
    request.op = .openAt → request.second = directoryFlags → request.first = Filesystem.cwd →
    request.left = ".".toUTF8 → object = before.workingDirectory
  exclusive : ∀ before after request observed object parent,
    kernel.step before request observed after → target before request observed after object →
    request.op = .openAt → request.second = newFileFlags →
    before.handles request.first = some parent →
    before.allocated object = false ∧ after.entries parent.object request.left = some object

-- §FS-host-boundary.ownership: An acknowledged descriptor is one instance of the same raw
-- introduction law. Its actual FD freshness, object and optional reply are all retained.
theorem OpenTargetContract.acknowledged {kernel : Contract} {semantics : NameSemanticsView}
    {initialObjects : ObjectId → Bool} {dataObjects : ObjectId → Prop}
    (targets : OpenTargetContract kernel semantics initialObjects dataObjects) (descriptors : DescriptorContract kernel)
    {before after : World} {request : Request} {reply : Reply} {fd : UInt64} {handle : Handle}
    (actual : kernel.step before request (some reply) after) (opening : request.op = .openAt)
    (recognized : descriptor reply = some fd) (live : after.handles fd = some handle) :
    targets.target before request (some reply) after handle.object := by
  have fresh := (descriptors.allocated_fresh _ _ _ _ _ actual (.inl opening) recognized).1
  rcases targets.introduced _ _ _ _ _ _ actual opening live with old | introduced
  · rw [fresh] at old
    cases old
  · exact introduced.2

-- §FS-host-boundary.ownership: Source lookup authorization is applied only to the actual
-- introduced object. Every old FD keeps its prior catalogue owner, even after error/loss.
theorem opened_filesystem_references_owned {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {semantics : NameSemanticsView}
    {initialObjects : ObjectId → Bool} {dataObjects : ObjectId → Prop}
    (targets : OpenTargetContract kernel semantics initialObjects dataObjects)
    {ticks : List (ActorTick runtime)} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply}
    (selected : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) (opening : request.op = .openAt)
    {first final : Family} {oldCatalogue newCatalogue : Catalogue runtime ticks}
    (consistent : tick.before.Consistent) (labels : ExistingLabels tick.before.shared tick.after.shared first final)
    (included : ∀ record ∈ oldCatalogue, record ∈ newCatalogue)
    (owned : EngineReferencesOwned runtime ticks tick.before first oldCatalogue)
    (authorized : ∀ object scope, targets.target (tick.before.project engine) request observed tick.after.shared object →
      final object = some scope → newCatalogue.Owns actor scope) :
    EngineReferencesOwned runtime ticks tick.after final newCatalogue := by
  have oldOwner : ∀ query prior, tick.before.actors query = some prior → ∀ fd handle scope,
      prior.references fd = some handle → final handle.object = some scope → newCatalogue.Owns query scope := by
    intro query prior beforePresent fd handle scope live privateObject
    have allocated := (consistent query prior beforePresent fd handle live).1
    have oldLabel : first handle.object = some scope := by
      rcases labels handle.object allocated with same | released
      · exact same.symm.trans privateObject
      · rw [privateObject] at released
        cases released
    exact (owned query prior beforePresent fd handle scope live oldLabel).weaken included
  rcases tick with ⟨action, before, after, operation⟩
  cases operation with
  | launch => cases selected
  | @returned β population owner current effect next reply world ownerPresent alive head actual =>
    dsimp only [ActorAction.eventFor] at selected
    split at selected
    · rename_i sameActor
      subst owner
      have engines := Option.some.inj (present.symm.trans ownerPresent)
      subst engine
      cases observed <;> cases selected
      intro query later afterPresent fd handle scope live privateObject
      by_cases sameQuery : query = actor
      · subst query
        simp only [Population.advance, Population.install, ite_eq_left] at afterPresent
        have same := Option.some.inj afterPresent
        subst later
        change world.handles fd = some handle at live
        rcases targets.introduced _ _ _ _ _ _ actual opening live with previous | introduced
        · exact oldOwner actor current ownerPresent fd handle scope previous privateObject
        · exact authorized handle.object scope introduced.2 privateObject
      · exact oldOwner query later (by
          simpa only [Population.advance, Population.install, ite_eq_right sameQuery] using afterPresent)
          fd handle scope live privateObject
    · cases selected
  | @lost β population owner current effect next world ownerPresent alive head actual =>
    dsimp only [ActorAction.eventFor] at selected
    split at selected
    · rename_i sameActor
      subst owner
      have engines := Option.some.inj (present.symm.trans ownerPresent)
      subst engine
      cases observed <;> cases selected
      intro query later afterPresent fd handle scope live privateObject
      by_cases sameQuery : query = actor
      · subst query
        simp only [Population.advance, Population.install, ite_eq_left] at afterPresent
        have same := Option.some.inj afterPresent
        subst later
        change world.handles fd = some handle at live
        rcases targets.introduced _ _ _ _ _ _ actual opening live with previous | introduced
        · exact oldOwner actor current ownerPresent fd handle scope previous privateObject
        · exact authorized handle.object scope introduced.2 privateObject
      · exact oldOwner query later (by
          simpa only [Population.advance, Population.install, ite_eq_right sameQuery] using afterPresent)
          fd handle scope live privateObject
    · cases selected
  | foreign | retire | nativeRetire => cases selected

-- §FS-host-boundary.ownership: A checked relative name can reach only an already-owned
-- private scope. Real mount/up/dot results and changing public-name comparisons are retained.
theorem relative_open_target_owned {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {semantics : NameSemanticsView}
    {initialObjects : ObjectId → Bool} {dataObjects : ObjectId → Prop}
    (targets : OpenTargetContract kernel semantics initialObjects dataObjects)
    {ticks : List (ActorTick runtime)} {population : Population} {family : Family} {catalogue : Catalogue runtime ticks}
    (graph : FamilyGraph population.shared family initialObjects dataObjects)
    (boundaries : ExactPrivateBoundaries semantics population.shared family)
    (owned : EngineReferencesOwned runtime ticks population family catalogue)
    {actor : ActorId} {engine : EngineState} (present : population.actors actor = some engine)
    {request : Request} {observed : Option Reply} {after : World} {object scope : ObjectId} {parent : Handle}
    (actual : kernel.step (population.project engine) request observed after)
    (target : targets.target (population.project engine) request observed after object)
    (opening : request.op = .openAt) (flags : request.second = directoryFlags ∨ request.second = readFlags)
    (parentLive : engine.references request.first = some parent)
    (component : Directories.component request.left = true) (publicName : PrivateNames.reservedBytes request.left = false)
    (privateObject : family object = some scope) : catalogue.Owns actor scope := by
  have data := graph.data object scope privateObject
  by_cases dot : request.left = ".".toUTF8
  · have same := targets.dot _ _ _ _ _ _ actual target opening flags parentLive dot
    exact owned actor engine present request.first parent scope parentLive (same ▸ privateObject)
  · by_cases up : request.left = "..".toUTF8
    · rcases targets.parent _ _ _ _ _ _ actual target opening flags parentLive up data with
        same | mounted | ⟨name, bound⟩
      · exact owned actor engine present request.first parent scope parentLive (same ▸ privateObject)
      · have young := graph.young _ _ privateObject
        rw [mounted] at young
        cases young

      · have currentPrivate := graph.descendants _ _ _ _ bound privateObject
        exact owned actor engine present request.first parent scope parentLive currentPrivate
    · rcases targets.child _ _ _ _ _ _ actual target opening flags parentLive component dot up data with
        ⟨storedName, bound, sameName⟩ | mounted
      · rcases graph.border _ _ _ _ bound privateObject with parentPrivate | reserved
        · exact owned actor engine present request.first parent scope parentLive parentPrivate
        · cases parentLabel : family parent.object with
          | some parentScope =>
            have childLabel := graph.descendants _ _ _ _ bound parentLabel
            have equal := Option.some.inj (childLabel.symm.trans privateObject)
            subst parentScope
            exact owned actor engine present request.first parent scope parentLive parentLabel
          | none =>
            have exactNames := boundaries _ _ _ _ bound privateObject parentLabel
            have same := sameName exactNames
            rw [same, publicName] at reserved
            cases reserved.1
      · have young := graph.young _ _ privateObject
        rw [mounted] at young
        cases young

-- §FS-host-boundary.ownership: No initialized mount cover belongs to a directory lifetime
-- born later. Private descendants therefore keep their parent's actual scope, even on loss.
theorem private_child_target_scope {kernel : Contract} {semantics : NameSemanticsView}
    {initialObjects : ObjectId → Bool} {dataObjects : ObjectId → Prop}
    (targets : OpenTargetContract kernel semantics initialObjects dataObjects)
    {before after : World} {request : Request} {observed : Option Reply} {object scope : ObjectId}
    {parent : Handle} {family : Family} (graph : FamilyGraph before family initialObjects dataObjects)
    (actual : kernel.step before request observed after) (target : targets.target before request observed after object)
    (opening : request.op = .openAt) (flags : request.second = directoryFlags ∨ request.second = readFlags)
    (parentLive : before.handles request.first = some parent) (parentPrivate : family parent.object = some scope)
    (component : Directories.component request.left = true) (notDot : request.left ≠ ".".toUTF8)
    (notUp : request.left ≠ "..".toUTF8) : family object = some scope := by
  obtain ⟨storedName, bound, compared⟩ := targets.young_child _ _ _ _ _ _ actual target opening flags parentLive
    component notDot notUp (graph.young _ _ parentPrivate) (graph.data _ _ parentPrivate)
  exact graph.descendants _ _ _ _ bound parentPrivate

end LeanCage.Host.Kernel
