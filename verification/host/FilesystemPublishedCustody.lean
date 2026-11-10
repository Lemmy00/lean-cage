import FilesystemCommitDelta
import FilesystemCreationState

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.publication: One actual committed rename releases only its own
-- source-derived family. The syscall may return an error or lose its reply afterwards;
-- remaining private boundaries retain their actual metadata and original ownership.
theorem source_published_namespace_custody {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {hostUid : Nat}
    (accounts : AccountContract kernel hostUid) (objects : ObjectLifetimeContract runtime)
    (metadata : LiveMetadataContract runtime child)
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    {resources : PrimitiveCommitResources runtime initial all tick actor engine request observed}
    {caps : Capabilities} {catalogue : Catalogue runtime all}
    (root : CommitRootAt runtime resources caps.family catalogue)
    (coverage : catalogue.Covers caps) (valid : catalogue.Valid tick.before.shared)
    {dataObjects directories : ObjectId → Prop} {foreignReferences : ForeignReferences}
    (state : NamespaceCustody (tick.before.project engine) caps hostUid initial.allocated dataObjects directories foreignReferences)
    (actual : kernel.step (tick.before.project engine) request observed tick.after.shared)
    (filesystem : actionFamily tick.action = .filesystem) (safe : AuthoritySafeAction tick.action)
    (moving : request.op = .renameNew)
    (change : DataChange dataObjects request (tick.before.project engine) tick.after.shared)
    (delta : CommitDelta resources root.root.object) :
    NamespaceCustody tick.after.shared (caps.published tick.after.shared root.root.object) hostUid
      initial.allocated dataObjects directories foreignReferences := by
  have allocation : ∀ object, (tick.before.project engine).allocated object = true → tick.after.shared.allocated object = true :=
    fun object => kernel.allocation_monotone _ _ _ _ object actual
  have gone : tick.after.shared.entries root.root.parent root.root.name ≠ some root.root.object := by
    have absent := delta.gone
    rw [root.container, root.name] at absent
    rw [absent]
    intro impossible
    cases impossible
  have member := root.active_root state.boundaries coverage valid
  have publicTarget : caps.family resources.parent.directory.handle.object = none := by
    rw [← resources.stage.sameParent]
    exact root.publicParent
  have requestSafe : AuthoritySafeRequest request := by intro setting; rw [moving] at setting; cases setting
  have privateDirectories : PrivateDirectoryAuthority tick.after.shared (clearFamily caps.family root.root.object) hostUid directories := by
    intro object scope information label known directory
    have oldLabel := (clear_family_some label).1
    have alive : ObjectAlive tick.after.shared object := ⟨information, known⟩
    obtain ⟨oldInformation, oldKnown⟩ := objects.filesystem _ _ _ _ _ actual
      (state.graph.live object scope oldLabel) alive
    obtain ⟨owner, mode⟩ := state.privateDirectories object scope oldInformation oldLabel oldKnown directory
    obtain ⟨later, laterKnown, authority⟩ := metadata.filesystem object oldInformation tick.operation filesystem safe alive oldKnown
    have sameInformation := Option.some.inj (known.symm.trans laterKnown)
    subst later
    exact ⟨authority.1.trans owner, (same_authority_mask authority 63 (by decide)).trans mode⟩
  exact ⟨published_capabilities_valid state.registry member gone allocation,
    family_graph_publish state.graph root.root.object resources.parent.directory.handle.object
      resources.source.source.commit.parent.name root.privateRoot publicTarget allocation delta.entries,
    root_boundaries_published state.boundaries state.graph root.privateRoot delta.entries,
    published_registry_authorities accounts actual requestSafe state.authorities,
    privateDirectories, clear_scope_directories state.scopes,
    ⟨fun object held => allocation _ (state.foreignSafe.1 object held),
      fun object scope held label => state.foreignSafe.2 object scope held (clear_family_some label).1⟩,
    data_change_well_formed change state.wellFormed allocation⟩

end LeanCage.Host.Kernel
