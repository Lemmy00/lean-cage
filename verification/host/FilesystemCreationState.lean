import FilesystemCreationDeltas
import FilesystemNamespaceState

namespace LeanCage.Host.Kernel
open Filesystem

theorem NamespaceCustody.project {world : Population} {engine : EngineState} {caps : Capabilities}
    {hostUid : Nat} {initialObjects : ObjectId → Bool} {dataObjects directories : ObjectId → Prop}
    {foreignReferences : ForeignReferences}
    (state : NamespaceCustody world.shared caps hostUid initialObjects dataObjects directories foreignReferences) :
    NamespaceCustody (world.project engine) caps hostUid initialObjects dataObjects directories foreignReferences := by
  exact ⟨state.registry, ⟨state.graph.live, state.graph.young, state.graph.data, state.graph.border,
    state.graph.descendants⟩, state.boundaries, state.authorities, state.privateDirectories,
    state.scopes, state.foreignSafe, state.wellFormed⟩

-- §FS-host-boundary.ownership: A source call with no committed namespace change retains the
-- old roots and metadata. Errors and lost replies are included in this exact-delta branch.
theorem source_unchanged_filesystem_custody {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {child : ChildPrimitive kernel} {hostUid : Nat}
    (accounts : AccountContract kernel hostUid) (objects : ObjectLifetimeContract runtime)
    (metadata : LiveMetadataContract runtime child)
    {tick : ActorTick runtime} {engine : EngineState} {request : Request} {observed : Option Reply}
    (actual : kernel.step (tick.before.project engine) request observed tick.after.shared)
    (filesystem : actionFamily tick.action = .filesystem) (safe : AuthoritySafeAction tick.action)
    (requestSafe : AuthoritySafeRequest request)
    {caps : Capabilities} {initialObjects : ObjectId → Bool} {dataObjects directories : ObjectId → Prop}
    {foreignReferences : ForeignReferences}
    (state : NamespaceCustody (tick.before.project engine) caps hostUid initialObjects dataObjects directories foreignReferences)
    (entries : tick.after.shared.entries = tick.before.shared.entries) :
    NamespaceCustody tick.after.shared (caps.retain tick.after.shared) hostUid
      initialObjects dataObjects directories foreignReferences := by
  have allocation : ∀ object, tick.before.shared.allocated object = true → tick.after.shared.allocated object = true :=
    fun object => kernel.allocation_monotone (tick.before.project engine) tick.after.shared request observed object actual
  have earlier : ∀ parent name object, tick.after.shared.entries parent name = some object →
      tick.before.shared.entries parent name = some object := by
    intro parent name object bound
    rw [entries] at bound
    exact bound
  have authorities : RootAuthorities (caps.retain tick.after.shared) tick.after.shared hostUid := by
    intro root member
    have kept := List.mem_filter.mp member
    have bound : tick.after.shared.entries root.parent root.name = some root.object := by simpa using kept.2
    exact root_authority_after accounts actual requestSafe (state.authorities root kept.1) bound
  have privateDirectories : PrivateDirectoryAuthority tick.after.shared caps.family hostUid directories := by
    intro object scope information label known directory
    have alive : ObjectAlive tick.after.shared object := ⟨information, known⟩
    obtain ⟨oldInformation, oldKnown⟩ := objects.filesystem _ _ _ _ _ actual
      (state.graph.live object scope label) alive
    obtain ⟨owner, mode⟩ := state.privateDirectories object scope oldInformation label oldKnown directory
    obtain ⟨later, laterKnown, authority⟩ := metadata.filesystem object oldInformation tick.operation filesystem safe alive oldKnown
    have sameInformation := Option.some.inj (known.symm.trans laterKnown)
    subst later
    exact ⟨authority.1.trans owner, (same_authority_mask authority 63 (by decide)).trans mode⟩
  refine ⟨retained_capabilities_valid state.registry allocation,
    family_graph_delete state.graph allocation earlier,
    root_boundaries_retain state.boundaries (by intro parent name object scope bound label; exact earlier _ _ _ bound),
    authorities, privateDirectories, state.scopes, ?_, ?_⟩
  · exact ⟨fun object held => allocation _ (state.foreignSafe.1 object held), state.foreignSafe.2⟩
  · intro parent name object bound
    have old := state.wellFormed _ _ _ (earlier _ _ _ bound)
    exact ⟨allocation _ old.1, allocation _ old.2⟩

-- §AR-host-boundary.interfaces: Preserve the exact existing mkdir consumer interface.
theorem source_unchanged_mkdir_custody {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {child : ChildPrimitive kernel} {hostUid : Nat}
    (accounts : AccountContract kernel hostUid) (objects : ObjectLifetimeContract runtime)
    (metadata : LiveMetadataContract runtime child)
    {tick : ActorTick runtime} {engine : EngineState} {request : Request} {observed : Option Reply}
    (actual : kernel.step (tick.before.project engine) request observed tick.after.shared)
    (filesystem : actionFamily tick.action = .filesystem) (safe : AuthoritySafeAction tick.action)
    (mkdir : request.op = .mkdirAt)
    {caps : Capabilities} {initialObjects : ObjectId → Bool} {dataObjects directories : ObjectId → Prop}
    {foreignReferences : ForeignReferences}
    (state : NamespaceCustody (tick.before.project engine) caps hostUid initialObjects dataObjects directories foreignReferences)
    (entries : tick.after.shared.entries = tick.before.shared.entries) :
    NamespaceCustody tick.after.shared (caps.retain tick.after.shared) hostUid
      initialObjects dataObjects directories foreignReferences :=
  source_unchanged_filesystem_custody accounts objects metadata actual filesystem safe
    (by intro setting; rw [mkdir] at setting; cases setting) state entries

-- §FS-host-boundary.ownership: This is the actual committed-source-mkdir case of the custody
-- fold. Parent/public authority is supplied by its source/anchor producer, not a helper frame.
theorem source_created_directory_custody {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {child : ChildPrimitive kernel} {hostUid : Nat}
    (accounts : AccountContract kernel hostUid) (objects : ObjectLifetimeContract runtime)
    (metadata : LiveMetadataContract runtime child) {directories : ObjectId → Prop}
    (types : CreationTypeContract kernel directories)
    {tick : ActorTick runtime} {engine : EngineState} {request : Request} {observed : Option Reply}
    (actual : kernel.step (tick.before.project engine) request observed tick.after.shared)
    (filesystem : actionFamily tick.action = .filesystem) (safe : AuthoritySafeAction tick.action)
    (mkdir : request.op = .mkdirAt) (mode : request.second = 448) (actor : ActorId)
    {caps : Capabilities} {initialObjects : ObjectId → Bool} {dataObjects : ObjectId → Prop}
    {foreignReferences : ForeignReferences}
    (state : NamespaceCustody (tick.before.project engine) caps hostUid initialObjects dataObjects directories foreignReferences)
    (delta : FreshDirectoryDelta dataObjects request (tick.before.project engine) tick.after.shared)
    (young : initialObjects delta.object = false) (publicParent : caps.family delta.parent.object = none)
    (reserved : PrivateNames.reservedBytes request.left = true) {parentInformation : Stat}
    (parentKnown : tick.before.shared.information delta.parent.object = some parentInformation)
    (trusted : Directories.trusted hostUid parentInformation = true) :
    NamespaceCustody tick.after.shared (caps.addRoot ⟨actor, delta.object, delta.parent.object, request.left⟩)
      hostUid initialObjects dataObjects directories foreignReferences := by
  let root : PrivateRoot := ⟨actor, delta.object, delta.parent.object, request.left⟩
  have allocation : ∀ object, (tick.before.project engine).allocated object = true →
      tick.after.shared.allocated object = true := fun object => kernel.allocation_monotone _ _ _ _ object actual
  have graph : FamilyGraph tick.after.shared (caps.addRoot root).family initialObjects dataObjects :=
    family_graph_adjoin state.graph state.wellFormed delta.object delta.object delta.parent.object request.left
      delta.fresh delta.allocated young delta.data delta.parentLive allocation delta.entries
      (.inr ⟨rfl, publicParent, reserved⟩)
  have rootSafe : AuthoritySafeRequest request := by intro setting; rw [mkdir] at setting; cases setting
  obtain ⟨childInformation, childKnown, owner, isDirectory, privateMode⟩ := accounts.mkdir_owner _ _ _ _ _ _
    actual mkdir mode delta.reference delta.fresh delta.bound
  obtain ⟨laterParent, laterParentKnown, parentSame⟩ := accounts.authority_existing _ _ _ _ _ _ actual rootSafe
    parentKnown (.inr ⟨request.left, delta.object, delta.bound⟩)
  have authorities : RootAuthorities (caps.addRoot root) tick.after.shared hostUid := by
    intro query member
    rcases List.mem_cons.mp member with rfl | old
    · exact ⟨childInformation, laterParent, childKnown, laterParentKnown, owner, privateMode, isDirectory,
        (same_authority_trusted hostUid parentSame).trans trusted⟩
    · exact root_authority_after accounts actual rootSafe (state.authorities query old)
        (delta.preserves_binding (state.registry.1 query old).2.2.1)
  have privateDirectories : PrivateDirectoryAuthority tick.after.shared (caps.addRoot root).family hostUid directories := by
    intro object scope information label known directory
    by_cases same : object = delta.object
    · subst object
      have sameInformation := Option.some.inj (known.symm.trans childKnown)
      subst information
      exact ⟨owner, privateMode⟩
    · have oldLabel : caps.family object = some scope := by
        simpa only [Capabilities.addRoot, root, ite_eq_right same] using label
      have alive : ObjectAlive tick.after.shared object := ⟨information, known⟩
      obtain ⟨oldInformation, oldKnown⟩ := objects.filesystem _ _ _ _ _ actual
        (state.graph.live object scope oldLabel) alive
      obtain ⟨oldOwner, oldMode⟩ := state.privateDirectories object scope oldInformation oldLabel oldKnown directory
      obtain ⟨later, laterKnown, authority⟩ := metadata.filesystem object oldInformation tick.operation filesystem safe alive oldKnown
      have sameInformation := Option.some.inj (known.symm.trans laterKnown)
      subst later
      exact ⟨authority.1.trans oldOwner, (same_authority_mask authority 63 (by decide)).trans oldMode⟩
  have newDirectory : directories delta.object := types.mkdir _ _ _ _ _ _ actual mkdir delta.reference delta.fresh delta.bound
  have foreignSafe : ForeignReferenceSafe tick.after.shared (caps.addRoot root).family directories foreignReferences := by
    constructor
    · intro object held
      exact allocation _ (state.foreignSafe.1 object held)
    · intro object scope held label
      by_cases same : object = delta.object
      · subst object
        have old := state.foreignSafe.1 delta.object held
        rw [delta.fresh] at old
        cases old
      · apply state.foreignSafe.2 object scope held
        simpa only [Capabilities.addRoot, root, ite_eq_right same] using label
  exact ⟨fresh_directory_register_valid delta actor state.registry publicParent allocation, graph,
    root_boundaries_adjoin state.boundaries state.wellFormed delta.fresh delta.entries, authorities,
    privateDirectories, set_scope_directories state.scopes newDirectory, foreignSafe,
    data_change_well_formed (.created delta.parent delta.object (.inl mkdir) delta.reference delta.parentLive
      delta.fresh delta.allocated delta.data delta.absent delta.entries) state.wellFormed allocation⟩

-- §FS-host-boundary.ownership: A public traversal may create a directory, but this never
-- grants it a private role. Existing private roots and every old family label are retained.
theorem source_created_public_directory_custody {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {child : ChildPrimitive kernel} {hostUid : Nat}
    (accounts : AccountContract kernel hostUid) (objects : ObjectLifetimeContract runtime)
    (metadata : LiveMetadataContract runtime child)
    {tick : ActorTick runtime} {engine : EngineState} {request : Request} {observed : Option Reply}
    (actual : kernel.step (tick.before.project engine) request observed tick.after.shared)
    (filesystem : actionFamily tick.action = .filesystem) (safe : AuthoritySafeAction tick.action)
    (mkdir : request.op = .mkdirAt)
    {caps : Capabilities} {initialObjects : ObjectId → Bool} {dataObjects directories : ObjectId → Prop}
    {foreignReferences : ForeignReferences}
    (state : NamespaceCustody (tick.before.project engine) caps hostUid initialObjects dataObjects directories foreignReferences)
    (delta : FreshDirectoryDelta dataObjects request (tick.before.project engine) tick.after.shared)
    (publicParent : caps.family delta.parent.object = none) :
    NamespaceCustody tick.after.shared (caps.retain tick.after.shared) hostUid
      initialObjects dataObjects directories foreignReferences := by
  have allocation : ∀ object, (tick.before.project engine).allocated object = true →
      tick.after.shared.allocated object = true := fun object => kernel.allocation_monotone _ _ _ _ object actual
  have requestSafe : AuthoritySafeRequest request := by intro setting; rw [mkdir] at setting; cases setting
  have authorities : RootAuthorities (caps.retain tick.after.shared) tick.after.shared hostUid := by
    intro root member
    have kept := List.mem_filter.mp member
    have bound : tick.after.shared.entries root.parent root.name = some root.object := by simpa using kept.2
    exact root_authority_after accounts actual requestSafe (state.authorities root kept.1) bound
  have privateDirectories : PrivateDirectoryAuthority tick.after.shared caps.family hostUid directories := by
    intro object scope information label known directory
    have alive : ObjectAlive tick.after.shared object := ⟨information, known⟩
    obtain ⟨oldInformation, oldKnown⟩ := objects.filesystem _ _ _ _ _ actual (state.graph.live object scope label) alive
    obtain ⟨owner, mode⟩ := state.privateDirectories object scope oldInformation label oldKnown directory
    obtain ⟨later, laterKnown, authority⟩ := metadata.filesystem object oldInformation tick.operation filesystem safe alive oldKnown
    have sameInformation := Option.some.inj (known.symm.trans laterKnown)
    subst later
    exact ⟨authority.1.trans owner, (same_authority_mask authority 63 (by decide)).trans mode⟩
  have boundaries := root_boundaries_public_birth state.boundaries state.graph delta.fresh delta.entries
  exact ⟨retained_capabilities_valid state.registry allocation,
    family_graph_public_adjoin state.graph delta.object delta.parent.object request.left delta.fresh publicParent
      allocation delta.entries,
    root_boundaries_retain boundaries (by intro parent name object scope bound label; exact bound), authorities,
    privateDirectories, state.scopes,
    ⟨fun object held => allocation _ (state.foreignSafe.1 object held), state.foreignSafe.2⟩,
    data_change_well_formed (.created delta.parent delta.object (.inl mkdir) delta.reference delta.parentLive
      delta.fresh delta.allocated delta.data delta.absent delta.entries) state.wellFormed allocation⟩

end LeanCage.Host.Kernel
