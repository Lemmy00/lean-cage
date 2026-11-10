import FilesystemStageReference
import FilesystemRootRetention

namespace LeanCage.Host.Kernel
open Filesystem

structure CommitRootAt {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (resources : PrimitiveCommitResources runtime initial all tick actor engine request observed)
    (family : Family) (catalogue : Catalogue runtime all) where
  root : PrivateRoot
  birth : RootBirth runtime all root
  member : Sigma.mk root birth ∈ catalogue
  owner : root.actor = actor
  stage : resources.stage.directory.handle.object = root.object
  container : resources.stage.container.handle.object = root.parent
  name : resources.source.source.commit.stage.name = root.name
  bound : tick.before.shared.entries resources.stage.container.handle.object
    resources.source.source.commit.stage.name = some root.object
  privateRoot : family root.object = some root.object
  publicParent : family resources.stage.container.handle.object = none
  owned : catalogue.Owns actor root.object
  sourceTick : ActorTick runtime
  sourceUse : PrimitiveRootUse runtime initial all sourceTick
  sourceBirth : birth.tick = sourceTick
  sourceOwner : root.actor = sourceUse.actor
  sourceQuiet : ∀ event ∈ engine.events.drop (sourceUse.engine.events.length + 1), NondestructiveEvent event

-- §FS-host-boundary.publication: Join the same selected commit resources, raw creation
-- and current registered custody. Its actual stage/parent/name are the SAME recorded
-- root lifetime, binding and owner; no chosen current root or future rename ACK is supplied.
theorem primitive_commit_root_from_resources {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (aliases : DirectoryAliasContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (environment : InterferenceContract kernel)
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
    (resources : PrimitiveCommitResources runtime initial all tick actor engine request observed)
    (moving : request.op = .renameNew) :
    Nonempty (CommitRootAt runtime resources prior.current.source.custody.caps.family
      prior.current.source.custody.catalogue) := by
  have selected : all[processed.length]? = some tick := by
    rw [whole, List.getElem?_append_right (by omega)]
    simp only [Nat.sub_self, List.getElem?_cons_zero]
  obtain ⟨source, sameActor, sameGuards, eventTrace⟩ := primitive_created_stage_continuation descriptors aliases
    lifetimes references environment journal selected present resources.adapter resources.source
  let earlier := source.earlier.source
  have earlierAt : processed[earlier.position]? = some earlier.tick := by
    simpa only [whole, List.getElem?_append_left earlier.earlier] using earlier.selected
  have earlierAction : earlier.tick.action.eventFor earlier.inputActor =
      some (Program.filesystemPrefixEvent (source.opening.request, some source.opening.reply)) := by
    simp only [earlier.action, ActorAction.eventFor, ↓reduceIte, Program.filesystemPrefixEvent]
  obtain ⟨root, birth, current, ordinal, member, owner, openedHandle, openedLive, openedObject, openedRaw⟩ :=
    source.root.opened_root descriptors lifetimes mounts journal prior whole earlierAt earlier.present
      earlierAction source.opening.opening source.opening.recognized
  have realLive : earlier.tick.after.shared.handles resources.source.source.commit.stage.directory.fd =
      some earlier.opening.handle := by
    rw [← earlier.shared_handles]
    exact earlier.opening.live
  have sameOpened : openedHandle = earlier.opening.handle := Option.some.inj (openedLive.symm.trans realLive)
  have openedObject : earlier.opening.handle.object = root.object :=
    (congrArg Handle.object sameOpened).symm.trans openedObject
  have retaining : ∀ event ∈ source.earlier.guards, RetainingEvent event := by
    rw [sameGuards]
    exact adapter_namespace_prefix_retaining resources.adapter (.inr (.inr (.inr (.inl moving))))
  have nondestructive : ∀ event ∈ source.earlier.guards, NondestructiveEvent event := by
    rw [sameGuards]
    exact adapter_namespace_prefix_nondestructive resources.adapter (.inr (.inr (.inr (.inl moving))))
  have currentStage := source.current_reference descriptors retaining
  have sameStage : earlier.opening.handle = resources.stage.directory.handle :=
    Option.some.inj (currentStage.symm.trans resources.stage.directory.live)
  have stage : resources.stage.directory.handle.object = root.object :=
    (congrArg Handle.object sameStage).symm.trans openedObject
  have parentBefore : earlier.opening.before.handles resources.source.source.commit.stage.container.fd =
      some source.root.use.parent := by
    rw [earlier.before]
    change earlier.input.references resources.source.source.commit.stage.container.fd = some source.root.use.parent
    have argument : source.opening.request.first = resources.source.source.commit.stage.container.fd :=
      congrArg Request.first source.opening.operation
    rw [← argument]
    exact source.root.reference
  have parentAfter := descriptors.allocate_existing _ _ _ _ _ _ earlier.opening.actual (.inl source.opening.opening) parentBefore
  have currentParent := source.current_kept_reference descriptors retaining _ _ parentAfter
  have sameParent : source.root.use.parent = resources.stage.container.handle :=
    Option.some.inj (currentParent.symm.trans resources.stage.container.live)
  have ownerUse : root.actor = source.root.use.actor := owner.trans source.root.sameActor.symm
  have currentPresent : tick.before.actors source.root.use.actor = some engine := by
    rw [source.root.sameActor, sameActor]
    exact present
  have quiet := source.source_nondestructive engine.events eventTrace nondestructive
  obtain ⟨bound, privateRoot, publicParent, owned, parent, name⟩ := prior.registered_birth_current lifetimes
    source.root.use birth current ownerUse member currentPresent quiet
  have container : resources.stage.container.handle.object = root.parent :=
    (congrArg Handle.object sameParent).symm.trans parent.symm
  have name : resources.source.source.commit.stage.name = root.name :=
    (congrArg Request.left source.opening.operation).symm.trans (source.root.sameName.trans name.symm)
  exact ⟨{
    root
    birth
    member
    owner := owner.trans sameActor
    stage
    container
    name
    bound := by rw [container, name]; exact bound
    privateRoot
    publicParent := by rw [container]; exact publicParent
    owned := by simpa only [source.root.sameActor, sameActor] using owned
    sourceTick := source.root.birthTick
    sourceUse := source.root.use
    sourceBirth := current
    sourceOwner := ownerUse
    sourceQuiet := quiet }⟩

-- §FS-host-boundary.publication: The actual raw rename call produces its own resources
-- before the root join; this includes returned error and loss without asserting a commit.
theorem actual_primitive_commit_root {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (aliases : DirectoryAliasContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (environment : InterferenceContract kernel)
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
    (moving : request.op = .renameNew) :
    ∃ resources : PrimitiveCommitResources runtime initial all tick actor engine request observed,
      Nonempty (CommitRootAt runtime resources prior.current.source.custody.caps.family
        prior.current.source.custody.catalogue) := by
  obtain ⟨resources⟩ := primitive_commit_resources descriptors aliases adapter moving
  exact ⟨resources, primitive_commit_root_from_resources descriptors aliases lifetimes references environment
    mounts journal prior whole present resources moving⟩

end LeanCage.Host.Kernel
