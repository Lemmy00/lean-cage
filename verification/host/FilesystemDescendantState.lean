import FilesystemCreationState

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: Directory and exclusive-file births below an actual private
-- parent inherit only that parent's scope. Lost/error acknowledgements do not erase births.
theorem source_created_descendant_custody {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {child : ChildPrimitive kernel} {hostUid : Nat}
    (accounts : AccountContract kernel hostUid) (objects : ObjectLifetimeContract runtime)
    (metadata : LiveMetadataContract runtime child) {directories : ObjectId → Prop}
    (types : CreationTypeContract kernel directories)
    {tick : ActorTick runtime} {engine : EngineState} {request : Request} {observed : Option Reply}
    (actual : kernel.step (tick.before.project engine) request observed tick.after.shared)
    (filesystem : actionFamily tick.action = .filesystem) (safe : AuthoritySafeAction tick.action)
    (operation : request.op = .mkdirAt ∨ (request.op = .openAt ∧ request.second = newFileFlags))
    (mode : request.op = .mkdirAt → request.second = 448)
    {caps : Capabilities} {initialObjects : ObjectId → Bool} {dataObjects : ObjectId → Prop}
    {foreignReferences : ForeignReferences} {scope : ObjectId}
    (state : NamespaceCustody (tick.before.project engine) caps hostUid initialObjects dataObjects
      directories foreignReferences)
    (delta : FreshDirectoryDelta dataObjects request (tick.before.project engine) tick.after.shared)
    (young : initialObjects delta.object = false) (parentPrivate : caps.family delta.parent.object = some scope) :
    NamespaceCustody tick.after.shared (caps.addDescendant delta.object scope) hostUid
      initialObjects dataObjects directories foreignReferences := by
  have allocation : ∀ object, (tick.before.project engine).allocated object = true →
      tick.after.shared.allocated object = true := fun object => kernel.allocation_monotone _ _ _ _ object actual
  have requestSafe : AuthoritySafeRequest request := by
    intro setting
    rcases operation with mkdir | opening
    · rw [mkdir] at setting; cases setting
    · rw [opening.1] at setting; cases setting
  have graph : FamilyGraph tick.after.shared (caps.addDescendant delta.object scope).family
      initialObjects dataObjects := family_graph_adjoin state.graph state.wellFormed delta.object scope
    delta.parent.object request.left delta.fresh delta.allocated young delta.data delta.parentLive allocation
    delta.entries (.inl parentPrivate)
  have authorities : RootAuthorities (caps.addDescendant delta.object scope) tick.after.shared hostUid := by
    intro root member
    exact root_authority_after accounts actual requestSafe (state.authorities root member)
      (delta.preserves_binding (state.registry.1 root member).2.2.1)
  have privateDirectories : PrivateDirectoryAuthority tick.after.shared
      (caps.addDescendant delta.object scope).family hostUid directories := by
    intro object owner information label known directory
    by_cases same : object = delta.object
    · subst object
      exact created_private_directory_authority accounts types actual operation mode delta.reference
        delta.fresh delta.bound directory information known
    · have oldLabel : caps.family object = some owner := by
        simpa only [Capabilities.addDescendant, setFamily, ite_eq_right same] using label
      have alive : ObjectAlive tick.after.shared object := ⟨information, known⟩
      obtain ⟨oldInformation, oldKnown⟩ := objects.filesystem _ _ _ _ _ actual
        (state.graph.live object owner oldLabel) alive
      obtain ⟨oldOwner, oldMode⟩ := state.privateDirectories object owner oldInformation oldLabel oldKnown directory
      obtain ⟨later, laterKnown, authority⟩ := metadata.filesystem object oldInformation tick.operation
        filesystem safe alive oldKnown
      have sameInformation := Option.some.inj (known.symm.trans laterKnown)
      subst later
      exact ⟨authority.1.trans oldOwner, (same_authority_mask authority 63 (by decide)).trans oldMode⟩
  have foreignSafe : ForeignReferenceSafe tick.after.shared (caps.addDescendant delta.object scope).family
      directories foreignReferences := by
    constructor
    · intro object held
      exact allocation _ (state.foreignSafe.1 object held)
    · intro object owner held label
      by_cases same : object = delta.object
      · subst object
        have old := state.foreignSafe.1 delta.object held
        rw [delta.fresh] at old
        cases old
      · apply state.foreignSafe.2 object owner held
        simpa only [Capabilities.addDescendant, setFamily, ite_eq_right same] using label
  exact ⟨register_descendant_at_commit state.registry delta.fresh allocation
      (fun root member => delta.preserves_binding (state.registry.1 root member).2.2.1),
    graph, root_boundaries_descendant state.boundaries state.wellFormed delta.fresh delta.parentLive
      parentPrivate delta.entries, authorities, privateDirectories,
    set_scope_directories state.scopes (state.scopes delta.parent.object scope parentPrivate), foreignSafe,
    data_change_well_formed (.created delta.parent delta.object operation delta.reference delta.parentLive
      delta.fresh delta.allocated delta.data delta.absent delta.entries) state.wellFormed allocation⟩

end LeanCage.Host.Kernel
