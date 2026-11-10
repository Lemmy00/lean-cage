import FilesystemUnchangedSource
import FilesystemPublicationProgress
import FilesystemByteNamespaceFrames

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: This is the physical deletion branch of one actual
-- source call. The application labels remain private after unlink, including
-- detached objects; no later pathname or cleanup-success observation is assumed.
theorem source_deleted_filesystem_custody {kernel : Contract} {sourceProgram : Program UInt32}
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
    (earlier : ∀ parent name object, tick.after.shared.entries parent name = some object →
      tick.before.shared.entries parent name = some object) :
    NamespaceCustody tick.after.shared (caps.retain tick.after.shared) hostUid
      initialObjects dataObjects directories foreignReferences := by
  have allocation : ∀ object, tick.before.shared.allocated object = true → tick.after.shared.allocated object = true :=
    fun object => kernel.allocation_monotone (tick.before.project engine) tick.after.shared request observed object actual
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

theorem unlink_removed_target {kernel : Contract} {semantics : NameSemanticsView}
    (names : ByteNamespaceFrameContract kernel semantics)
    {before after : World} {request : Request} {observed : Option Reply}
    (actual : kernel.step before request observed after) (removing : request.op = .unlinkAt)
    (component : Directories.component request.left = true)
    (comparison : ByteNamespaceOperands semantics before request)
    {parent object : ObjectId} {name : ByteArray} (bound : before.entries parent name = some object)
    (removed : after.entries parent name ≠ some object) : NamesEntry before request.first request.left parent name := by
  apply Classical.byContradiction
  intro untouched
  have frame := names.entry _ _ _ _ parent name actual
    (by simpa only [ComponentRequest, removing] using component)
    comparison
    (by simpa only [TouchesEntry, removing] using untouched)
  exact removed (frame.trans bound)

theorem unlink_delta_deletes {dataObjects : ObjectId → Prop} {before after : World}
    {request : Request} (change : DataChange dataObjects request before after)
    (removing : request.op = .unlinkAt) :
    ∀ parent name object, after.entries parent name = some object → before.entries parent name = some object := by
  intro parent name object bound
  cases change with
  | unchanged entries => rwa [entries] at bound
  | created _ _ operation =>
    rcases operation with mkdir | opening
    · rw [removing] at mkdir; cases mkdir
    · rw [removing] at opening; cases opening.1
  | removed operation earlier => exact earlier _ _ _ bound
  | renamed _ _ _ operation => rw [removing] at operation; cases operation

-- §FS-host-boundary.ownership: Authorization refers only to the actual resolved
-- parent/name and its current binding. The source producer supplies it for its
-- private descendants or for its own exact registered root removal.
theorem owned_unlink_registered_custody_with_step {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    (namespaceLaws : ByteNamespaceFrameContract kernel semantics) (descriptors : DescriptorContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (sdk : RuntimeDescriptorContract runtime) (accounts : AccountContract kernel hostUid)
    (objects : ObjectLifetimeContract runtime) (metadata : LiveMetadataContract runtime child)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {final : Population} {all processed : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply} {parent : Handle}
    (selected : all[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) (removing : request.op = .unlinkAt)
    (parentLive : engine.references request.first = some parent)
    (component : Directories.component request.left = true)
    (comparison : (semantics.at tick.before.shared parent.object).byteExact)
    (earlier : ∀ parent name object, tick.after.shared.entries parent name = some object →
      tick.before.shared.entries parent name = some object)
    {foreignReferences : ForeignReferences} {currentNative : NativeProcesses}
    (prior : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative)
    (authorized : ∀ object scope, tick.before.shared.entries parent.object request.left = some object →
      prior.current.source.custody.caps.family object = some scope →
      prior.current.source.custody.catalogue.Owns actor scope) :
    ∃ next : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
        foreignReferences (processed ++ [tick]) tick.after currentNative,
      next.current.source.custody.catalogue = prior.current.source.custody.catalogue ∧
      next.current.source.custody.caps.family = prior.current.source.custody.caps.family ∧
      CustodyOwnershipStep next.current.source.custody.catalogue tick
        prior.current.source.custody.caps.family next.current.source.custody.caps.family := by
  have actual := selected_filesystem_step tick action present
  have filesystem := selected_filesystem_action_family action
  have safe := selected_primitive_action_authority journal selected
  have requestSafe : AuthoritySafeRequest request := by intro setting; rw [removing] at setting; cases setting
  have state := source_deleted_filesystem_custody accounts objects metadata actual filesystem safe requestSafe
    prior.current.source.custody.namespaceState.project earlier
  have names := filesystem_registered_root_names lookup filesystem safe
    prior.current.source.custody.namespaceState.registry prior.current.source.custody.names
  have allocation := fun object => kernel.allocation_monotone (tick.before.project engine)
    tick.after.shared request observed object actual
  have owned := retained_filesystem_references_owned descriptors action
    (by rw [removing]; simp [RetainsDescriptors]) prior.current.source.custody.consistent
    (unchanged_existing_labels _ _ _) (by intro record member; exact member) prior.current.source.custody.references
  let next := prior.current.source.custody.advance descriptors lifetimes references
    (prior.current.source.custody.caps.retain tick.after.shared) prior.current.source.custody.catalogue
    state names (catalogue_retained_covers prior.current.source.custody.coverage)
    (catalogue_advance_valid prior.current.source.custody.valid allocation) owned .same
  have ownership : CustodyOwnershipStep next.catalogue tick prior.current.source.custody.caps.family next.caps.family := by
    constructor
    · intro target name object scope bound label removed
      obtain ⟨actualParent, live, parentObject, selectedName⟩ :=
        unlink_removed_target namespaceLaws actual removing component
          (byte_unlink_operands removing parentLive comparison) bound removed
      have same : actualParent = parent := Option.some.inj (live.symm.trans parentLive)
      have inputBinding : tick.before.shared.entries parent.object request.left = some object := by
        rw [← same, parentObject, selectedName]
        exact bound
      exact ⟨actor, request, observed, action, .inl removing, authorized object scope inputBinding label⟩
    · intro object scope allocated label released
      exact False.elim (released label)
  let afterSource := prior.current.source.advance next (by intro record member; exact member) ownership
  let result := prior.sourceStep sdk lifetimes afterSource (by
      intro owner handles closeExec directory impossible
      rw [impossible] at action
      cases action) (unchanged_existing_labels _ _ _) rfl ownership
    (no_root_use_of_other_operation action (by rw [removing]; decide))
  exact ⟨result, rfl, rfl, ownership⟩


-- §AR-host-boundary.interfaces: Preserve the original deletion consumer type;
-- the stronger source-fold sibling also retains the exact ownership row.
theorem owned_unlink_registered_custody {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    (namespaceLaws : ByteNamespaceFrameContract kernel semantics) (descriptors : DescriptorContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (sdk : RuntimeDescriptorContract runtime) (accounts : AccountContract kernel hostUid)
    (objects : ObjectLifetimeContract runtime) (metadata : LiveMetadataContract runtime child)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {final : Population} {all processed : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply} {parent : Handle}
    (selected : all[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) (removing : request.op = .unlinkAt)
    (parentLive : engine.references request.first = some parent)
    (component : Directories.component request.left = true)
    (comparison : (semantics.at tick.before.shared parent.object).byteExact)
    (earlier : ∀ parent name object, tick.after.shared.entries parent name = some object →
      tick.before.shared.entries parent name = some object)
    {foreignReferences : ForeignReferences} {currentNative : NativeProcesses}
    (prior : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative)
    (authorized : ∀ object scope, tick.before.shared.entries parent.object request.left = some object →
      prior.current.source.custody.caps.family object = some scope →
      prior.current.source.custody.catalogue.Owns actor scope) :
    ∃ next : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
        foreignReferences (processed ++ [tick]) tick.after currentNative,
      next.current.source.custody.catalogue = prior.current.source.custody.catalogue ∧
      next.current.source.custody.caps.family = prior.current.source.custody.caps.family := by
  obtain ⟨next, catalogue, labels, ownership⟩ := owned_unlink_registered_custody_with_step
    namespaceLaws descriptors lifetimes references sdk accounts objects metadata lookup journal selected
    action present removing parentLive component comparison earlier prior authorized
  exact ⟨next, catalogue, labels⟩

-- §FS-host-boundary.ownership: Cleanup of a current private descendant obtains
-- its owner from the actual retained parent reference. Its unlinks keep private
-- labels, including orphaned objects, and extend the same publication history.
theorem private_parent_unlink_registered_publication {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    (namespaceLaws : ByteNamespaceFrameContract kernel semantics) (descriptors : DescriptorContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (sdk : RuntimeDescriptorContract runtime) (accounts : AccountContract kernel hostUid)
    (objects : ObjectLifetimeContract runtime) (metadata : LiveMetadataContract runtime child)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {final : Population} {all processed : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply} {parent : Handle} {scope : ObjectId}
    (selected : all[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) (removing : request.op = .unlinkAt)
    (parentLive : engine.references request.first = some parent)
    (component : Directories.component request.left = true)
    (comparison : (semantics.at tick.before.shared parent.object).byteExact)
    (change : DataChange dataObjects request (tick.before.project engine) tick.after.shared)
    {foreignReferences : ForeignReferences} {currentNative : NativeProcesses}
    (prior : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative)
    (privateParent : prior.custody.current.source.custody.caps.family parent.object = some scope) :
    Nonempty (RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after currentNative) := by
  have owner := prior.custody.current.source.custody.references actor engine present request.first parent scope
    parentLive privateParent
  obtain ⟨next, catalogue, labels⟩ := owned_unlink_registered_custody namespaceLaws descriptors lifetimes references sdk
    accounts objects metadata lookup journal selected action present removing parentLive component comparison
    (by intro parent name object bound; exact unlink_delta_deletes change removing parent name object bound) prior.custody (by
      intro object ownerScope bound label
      have descendant := prior.custody.current.source.custody.namespaceState.graph.descendants _ _ _ _ bound privateParent
      have same : scope = ownerScope := Option.some.inj (descendant.symm.trans label)
      exact same ▸ owner)
  exact ⟨prior.preserved next catalogue (by intro object allocated; rw [labels])⟩

end LeanCage.Host.Kernel
