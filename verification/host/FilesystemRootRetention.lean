import FilesystemRootOpenReceipt

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: One actual source row has one input/request/parent.
-- This identity uses the stored tick and actor, never finite inode observations.
theorem RootBirth.same_source_use {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {root : PrivateRoot} (birth : RootBirth runtime all root) (use : PrimitiveRootUse runtime initial all tick)
    (current : birth.tick = tick) (owner : root.actor = use.actor) :
    birth.engine = use.engine ∧ birth.request = use.request ∧ birth.observed = some use.reply ∧
      birth.parent = use.parent ∧ root.parent = use.parent.object ∧ root.name = use.request.left := by
  have bornPresent : tick.before.actors use.actor = some birth.engine := by
    rw [← owner, ← current]
    exact birth.present
  have engine : birth.engine = use.engine := Option.some.inj (bornPresent.symm.trans use.present)
  have birthAction : tick.action.eventFor use.actor = some (Program.filesystemPrefixEvent (birth.request, birth.observed)) := by
    rw [← owner, ← current]
    exact birth.action
  have event := Option.some.inj (birthAction.symm.trans use.action)
  have decoded := congrArg PrimitiveFilesystem.filesystemEvent? event
  have pair : (birth.request, birth.observed) = (use.request, some use.reply) := by
    simpa only [PrimitiveFilesystem.filesystem_event_decode, Option.some.injEq] using decoded
  have request : birth.request = use.request := congrArg Prod.fst pair
  have observed : birth.observed = some use.reply := congrArg Prod.snd pair
  have reference : use.engine.references use.request.first = some birth.parent := by
    rw [← engine, ← request]
    exact birth.reference
  have parent : birth.parent = use.parent := Option.some.inj (reference.symm.trans use.reference)
  exact ⟨engine, request, observed, parent,
    birth.parentObject.symm.trans (congrArg Handle.object parent), birth.name.symm.trans (congrArg Request.left request)⟩

-- §FS-host-boundary.ownership: Keep this exact catalogue birth through the actual
-- owner's nondestructive source suffix. Other actors are handled by the constructed
-- ownership journal; no whole private-region frame is an external premise.
theorem RegisteredCustodyState.registered_birth_current {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (lifetimes : LifetimeContract runtime)
    {initial : World} {all processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignReferences : ForeignReferences} {population : Population} {native : NativeProcesses}
    (state : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed population native)
    {tick : ActorTick runtime} (use : PrimitiveRootUse runtime initial all tick)
    {root : PrivateRoot} (birth : RootBirth runtime all root)
    (current : birth.tick = tick) (owner : root.actor = use.actor)
    (member : Sigma.mk root birth ∈ state.current.source.custody.catalogue)
    {engine : EngineState} (present : population.actors use.actor = some engine)
    (source : ∀ event ∈ engine.events.drop (use.engine.events.length + 1), NondestructiveEvent event) :
    population.shared.entries root.parent root.name = some root.object ∧
      state.current.source.custody.caps.family root.object = some root.object ∧
      state.current.source.custody.caps.family root.parent = none ∧
      state.current.source.custody.catalogue.Owns use.actor root.object ∧
      root.parent = use.parent.object ∧ root.name = use.request.left := by
  obtain ⟨sameEngine, sameRequest, sameObserved, sameParent, parent, name⟩ := birth.same_source_use use current owner
  obtain ⟨scopeCut⟩ := state.current.births (Sigma.mk root birth) member
  obtain ⟨born, bornPresent, appended⟩ := source_event_after tick use.action use.present
  have bornPresent : birth.tick.after.actors use.actor = some born := by rwa [current]
  have count : born.events.length = use.engine.events.length + 1 := by
    simp only [appended, List.length_append, List.length_singleton]
  have actualSource := actor_interval_nondestructive_profile scopeCut.ownership.actual bornPresent present
    (by rw [count]; exact source)
  have owned : state.current.source.custody.catalogue.Owns use.actor root.object :=
    ⟨Sigma.mk root birth, member, owner, rfl⟩
  obtain ⟨bound, privateRoot⟩ := scopeCut.ownership.private_binding_retained_nondestructive lifetimes
    state.current.source.custody.valid owned birth.fresh.2 scopeCut.privateRoot birth.bound actualSource
  exact ⟨bound, privateRoot, scopeCut.parentPublic, owned, parent, name⟩

-- §FS-host-boundary.ownership: An intermediate constructed snapshot registers the
-- SAME selected mkdir. Its independently stored catalogue proof cannot substitute
-- another directory lifetime; both records name the same actual post-mkdir binding.
theorem RegisteredCustodyState.source_birth_current {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (lifetimes : LifetimeContract runtime)
    {initial : World} {all processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignReferences : ForeignReferences} {population : Population} {native : NativeProcesses}
    (state : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed population native)
    {position : Nat} {tick : ActorTick runtime} (selected : processed[position]? = some tick)
    (use : PrimitiveRootUse runtime initial all tick)
    {root : PrivateRoot} (birth : RootBirth runtime all root)
    (current : birth.tick = tick) (owner : root.actor = use.actor)
    {engine : EngineState} (present : population.actors use.actor = some engine)
    (source : ∀ event ∈ engine.events.drop (use.engine.events.length + 1), NondestructiveEvent event) :
    population.shared.entries root.parent root.name = some root.object ∧
      state.current.source.custody.caps.family root.object = some root.object ∧
      state.current.source.custody.catalogue.Owns use.actor root.object := by
  obtain ⟨chosen, actualBirth, sameTick, ordinal, member, actualOwner, parent, name, scope⟩ :=
    state.root_scope selected use
  obtain ⟨bound, privateRoot, publicParent, owned, actualParent, actualName⟩ :=
    state.registered_birth_current lifetimes use actualBirth sameTick actualOwner member present source
  obtain ⟨sameEngine, sameRequest, sameObserved, sameParent, birthParent, birthName⟩ :=
    birth.same_source_use use current owner
  have first : tick.after.shared.entries use.parent.object use.request.left = some root.object := by
    simpa only [current, birthParent, birthName] using birth.bound
  have second : tick.after.shared.entries use.parent.object use.request.left = some chosen.object := by
    simpa only [sameTick, parent, name] using actualBirth.bound
  have identity : chosen.object = root.object := Option.some.inj (second.symm.trans first)
  refine ⟨?_, by simpa only [identity] using privateRoot, by simpa only [identity] using owned⟩
  simpa only [parent, name, ← birthParent, ← birthName, identity] using bound

end LeanCage.Host.Kernel
