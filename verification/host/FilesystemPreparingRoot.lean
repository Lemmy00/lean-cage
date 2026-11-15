import FilesystemPreparingSource
import FilesystemRootRetention

namespace LeanCage.Host.Kernel
open Filesystem

structure PreparingRootAt {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    {adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed}
    {call : PublicationPreparing.Call adapter.occurrence.logicalBefore request} {position : Nat}
    (resources : PreparingStageResources adapter call position) (family : Family) (catalogue : Catalogue runtime all) where
  root : PrivateRoot
  birth : RootBirth runtime all root
  member : Sigma.mk root birth ∈ catalogue
  owner : root.actor = actor
  directory : resources.source.earlier.source.opening.handle.object = root.object
  container : resources.source.root.use.parent.object = root.parent
  name : call.context.stage.name = root.name
  bound : tick.before.shared.entries resources.source.root.use.parent.object call.context.stage.name = some root.object
  privateRoot : family root.object = some root.object
  publicParent : family resources.source.root.use.parent.object = none
  owned : catalogue.Owns actor root.object
  sourceBirth : birth.tick = resources.source.root.birthTick
  sourceOwner : root.actor = resources.source.root.use.actor
  sourceQuiet : ∀ event ∈ engine.events.drop (resources.source.root.use.engine.events.length + 1), NondestructiveEvent event

-- §FS-host-boundary.ownership: The SAME in-progress preparation selects its
-- actual source-registered root, still-bound raw name and private family.
-- No future preparation, publication or cleanup outcome is required.
theorem actual_preparing_root_from_resources {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    {initial : World} {final : Population} {all processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    (mounts : MountContract kernel initial.allocated)
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {native : NativeProcesses}
    (prior : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before native)
    {trailing : List (ActorTick runtime)} (whole : all = processed ++ tick :: trailing)
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (present : tick.before.actors actor = some engine)
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    {call : PublicationPreparing.Call adapter.occurrence.logicalBefore request}
    (resources : PreparingStageResources adapter call processed.length)
    (primary : request = adapter.occurrence.primary) :
    Nonempty (PreparingRootAt resources prior.current.source.custody.caps.family prior.current.source.custody.catalogue) := by
  let source := resources.source
  let earlier := source.earlier.source
  have earlierAt : processed[earlier.position]? = some earlier.tick := by
    simpa only [whole, List.getElem?_append_left earlier.earlier] using earlier.selected
  have earlierAction : earlier.tick.action.eventFor earlier.inputActor =
      some (Program.filesystemPrefixEvent (source.opening.request, some source.opening.reply)) := by
    simp only [earlier.action, ActorAction.eventFor, ↓reduceIte, Program.filesystemPrefixEvent]
  obtain ⟨root, birth, current, ordinal, member, owner, openedHandle, openedLive, openedObject, openedRaw⟩ :=
    source.root.opened_root descriptors lifetimes mounts journal prior whole earlierAt earlier.present
      earlierAction source.opening.opening source.opening.recognized
  have realLive : earlier.tick.after.shared.handles call.context.stage.directory.fd = some earlier.opening.handle := by
    rw [← earlier.shared_handles]
    exact earlier.opening.live
  have sameOpened : openedHandle = earlier.opening.handle := Option.some.inj (openedLive.symm.trans realLive)
  have directory : earlier.opening.handle.object = root.object :=
    (congrArg Handle.object sameOpened).symm.trans openedObject
  have ownerUse : root.actor = source.root.use.actor := owner.trans source.root.sameActor.symm
  have currentPresent : tick.before.actors source.root.use.actor = some engine := by
    rw [source.root.sameActor, resources.sameActor]
    exact present
  have quiet := source.source_nondestructive engine.events resources.eventTrace (resources.guards_nondestructive primary)
  obtain ⟨bound, privateRoot, publicParent, owned, parent, name⟩ := prior.registered_birth_current lifetimes
    source.root.use birth current ownerUse member currentPresent quiet
  have actualName : call.context.stage.name = root.name :=
    (congrArg Request.left source.opening.operation).symm.trans (source.root.sameName.trans name.symm)
  exact ⟨{
    root
    birth
    member
    owner := owner.trans resources.sameActor
    directory
    container := parent.symm
    name := actualName
    bound := by rw [← parent, actualName]; exact bound
    privateRoot
    publicParent := by rw [← parent]; exact publicParent
    owned := Eq.mp (congrArg (fun who => prior.current.source.custody.catalogue.Owns who root.object)
      (source.root.sameActor.trans resources.sameActor)) owned
    sourceBirth := current
    sourceOwner := ownerUse
    sourceQuiet := quiet }⟩

end LeanCage.Host.Kernel
