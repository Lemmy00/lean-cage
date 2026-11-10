import FilesystemCommitRoot

namespace LeanCage.Host.Kernel
open Filesystem

private theorem root_ext {first last : PrivateRoot}
    (actor : first.actor = last.actor) (object : first.object = last.object)
    (parent : first.parent = last.parent) (name : first.name = last.name) : first = last := by
  cases first
  cases last
  cases actor
  cases object
  cases parent
  cases name
  rfl

-- §FS-host-boundary.ownership: Its current private boundary retains the active capability,
-- while the full catalogue also keeps old/published births. The actor is fixed by that
-- same catalogue's lifetime ownership, not a second root role.
theorem CommitRootAt.active_root {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    {resources : PrimitiveCommitResources runtime initial all tick actor engine request observed}
    {caps : Capabilities} {catalogue : Catalogue runtime all}
    (source : CommitRootAt runtime resources caps.family catalogue)
    (boundaries : RootBoundaries caps tick.before.shared)
    (coverage : catalogue.Covers caps) (valid : catalogue.Valid tick.before.shared) : source.root ∈ caps.roots := by
  obtain ⟨record, member, parent, name, object⟩ := boundaries _ _ _ _ source.bound source.privateRoot source.publicParent
  have owned := catalogue_scope_owner coverage member
  have owned : catalogue.Owns record.actor source.root.object := object ▸ owned
  have owner := catalogue_unique_owner valid owned source.owned
  have same : record = source.root := root_ext (owner.trans source.owner.symm) object
    (parent.trans source.container) (name.trans source.name)
  exact same ▸ member

theorem CommitRootAt.components {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    {resources : PrimitiveCommitResources runtime initial all tick actor engine request observed}
    {family : Family} {catalogue : Catalogue runtime all}
    (_source : CommitRootAt runtime resources family catalogue) : ComponentRequest request := by
  have target := selected_parent_component resources.source.source.target true resources.source.source.commit.selected
  have stage := selected_fresh_component resources.source.source.commit.parent resources.source.source.commit.created
  exact (congrArg ComponentRequest resources.source.source.commit.operation).mpr ⟨stage.1, target.1⟩

theorem CommitRootAt.root_entry {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    {resources : PrimitiveCommitResources runtime initial all tick actor engine request observed}
    {family : Family} {catalogue : Catalogue runtime all}
    (source : CommitRootAt runtime resources family catalogue) :
    RootEntry (tick.before.project engine) request source.root := by
  have fd : request.first = resources.source.source.commit.stage.container.fd :=
    congrArg Request.first resources.source.source.commit.operation
  have name : request.left = resources.source.source.commit.stage.name :=
    congrArg Request.left resources.source.source.commit.operation
  exact ⟨resources.stage.container.handle, by rw [fd]; exact resources.stage.container.live,
    source.container, name.trans source.name⟩

-- §FS-host-boundary.publication: Every source rename is removal of its own root;
-- this role does not depend on whether the actual call commits, returns error or loses reply.
theorem CommitRootAt.removal_owned {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    {resources : PrimitiveCommitResources runtime initial all tick actor engine request observed}
    {caps : Capabilities} {catalogue : Catalogue runtime all}
    (source : CommitRootAt runtime resources caps.family catalogue)
    (boundaries : RootBoundaries caps tick.before.shared) (coverage : catalogue.Covers caps)
    (valid : catalogue.Valid tick.before.shared) : OwnedRemoval caps (tick.before.project engine) actor request :=
  .inl ⟨source.root, source.active_root boundaries coverage valid, source.owner, source.root_entry⟩

-- §FS-host-boundary.publication: Derive both actual move roles from the SAME source
-- operands and current binding. No arbitrary caller-chosen family may be published.
theorem CommitRootAt.publication_move {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    {resources : PrimitiveCommitResources runtime initial all tick actor engine request observed}
    {family : Family} {catalogue : Catalogue runtime all}
    (source : CommitRootAt runtime resources family catalogue) :
    PublicationMove family request (tick.before.project engine) := by
  intro first target object firstLive targetLive bound
  have firstFd : request.first = resources.source.source.commit.stage.container.fd :=
    congrArg Request.first resources.source.source.commit.operation
  have targetFd : request.second = resources.source.source.commit.parent.directory.fd :=
    congrArg Request.second resources.source.source.commit.operation
  have name : request.left = resources.source.source.commit.stage.name :=
    congrArg Request.left resources.source.source.commit.operation
  have firstSame : first = resources.stage.container.handle :=
    Option.some.inj ((firstFd ▸ firstLive).symm.trans resources.stage.container.live)
  have targetSame : target = resources.parent.directory.handle :=
    Option.some.inj ((targetFd ▸ targetLive).symm.trans resources.stage.parentLive)
  have actualBound : (tick.before.project engine).entries first.object request.left = some source.root.object := by
    change tick.before.shared.entries first.object request.left = some source.root.object
    rw [firstSame, name]
    exact source.bound
  have sameObject : object = source.root.object := Option.some.inj (bound.symm.trans actualBound)
  constructor
  · rw [targetSame, ← resources.stage.sameParent]
    exact source.publicParent
  · exact .inr (sameObject ▸ source.privateRoot)

end LeanCage.Host.Kernel
