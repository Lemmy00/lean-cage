import FilesystemRegisteredCustody

namespace LeanCage.Host.Kernel
open Filesystem

variable {sourceProgram : Program UInt32}

-- §AR-host-boundary.primitives: This law describes ONE parent runtime operation's
-- kernel linearization row. Child progress has its own shared-journal rows, including
-- while the parent waits; this is not a frame over a spawn/wait interval or callback.
structure RuntimeNamespaceContract {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram) : Prop where
  entries : ∀ {β : Type} actor (effect : Effect β) observed before after,
    RuntimeEffect effect → runtime.other actor effect observed before after → after.entries = before.entries

private theorem returned_runtime {β : Type} {actor : ActorId} {effect : Effect β} {reply : β}
    (kind : actionFamily (.returned actor effect reply) = .runtime) : RuntimeEffect effect := by
  cases effect <;> simp_all [actionFamily, RuntimeEffect]

private theorem lost_runtime {β : Type} {actor : ActorId} {effect : Effect β}
    (kind : actionFamily (.lost actor effect) = .runtime) : RuntimeEffect effect := by
  cases effect <;> simp_all [actionFamily, RuntimeEffect]

private theorem runtime_operation_entries {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (laws : RuntimeNamespaceContract runtime) {β : Type} {actor : ActorId} {effect : Effect β}
    {reply : Option β} {before after : World} (kind : RuntimeEffect effect)
    (actual : ActorOperation runtime actor effect reply before after) : after.entries = before.entries := by
  cases effect with
  | filesystem => exact False.elim kind
  | spawn | read | wait | terminate | tryWait | descriptor => exact laws.entries _ _ _ _ _ kind actual

private theorem runtime_operation_reference {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (laws : RuntimeDescriptorContract runtime) {β : Type} {actor : ActorId} {effect : Effect β}
    {reply : Option β} {before after : World} (kind : RuntimeEffect effect)
    (actual : ActorOperation runtime actor effect reply before after) {fd : UInt64} {handle : Handle}
    (live : after.handles fd = some handle) : before.handles fd = some handle := by
  cases effect with
  | filesystem => exact False.elim kind
  | spawn | read | wait | terminate | tryWait | descriptor => exact laws.new_reference _ _ _ _ _ _ _ actual live

theorem runtime_entries {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (laws : RuntimeNamespaceContract runtime) {before after : Population} {action : ActorAction}
    (actual : ActorStep runtime action before after) (kind : actionFamily action = .runtime) :
    after.shared.entries = before.shared.entries := by
  cases actual with
  | launch | foreign | retire | nativeRetire => cases kind
  | returned present running head operation =>
    have unchanged := runtime_operation_entries laws (returned_runtime kind) operation
    exact unchanged
  | lost present running head operation =>
    have unchanged := runtime_operation_entries laws (lost_runtime kind) operation
    exact unchanged

theorem runtime_references_from {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (laws : RuntimeDescriptorContract runtime) {before after : Population} {action : ActorAction}
    (actual : ActorStep runtime action before after) (kind : actionFamily action = .runtime) :
    EngineReferencesFrom before after := by
  cases actual with
  | launch | foreign | retire | nativeRetire => cases kind
  | @returned β population owner current effect next reply world ownerPresent running head operation =>
    intro actor engine afterPresent fd handle held
    by_cases same : actor = owner
    · subst actor
      simp only [Population.advance, Population.install, ite_eq_left] at afterPresent
      have identity := Option.some.inj afterPresent
      subst engine
      exact ⟨current, ownerPresent, runtime_operation_reference laws (returned_runtime kind) operation held⟩
    · exact ⟨engine, by simpa only [Population.advance, Population.install, ite_eq_right same] using afterPresent, held⟩
  | @lost β population owner current effect next world ownerPresent running head operation =>
    intro actor engine afterPresent fd handle held
    by_cases same : actor = owner
    · subst actor
      simp only [Population.advance, Population.install, ite_eq_left] at afterPresent
      have identity := Option.some.inj afterPresent
      subst engine
      exact ⟨current, ownerPresent, runtime_operation_reference laws (lost_runtime kind) operation held⟩
    · exact ⟨engine, by simpa only [Population.advance, Population.install, ite_eq_right same] using afterPresent, held⟩

-- §FS-host-boundary.ownership: A source runtime row retains the same actual root/catalogue,
-- while preserving independent child progress and final inode/handle retirement.
theorem runtime_ownership_prefix {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    (namespaces : RuntimeNamespaceContract runtime) (sdk : RuntimeDescriptorContract runtime) (descriptors : DescriptorContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (objects : ObjectLifetimeContract runtime) (metadata : LiveMetadataContract runtime child)
    (heldMetadata : GlobalAuthorityContract runtime child)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {ticks processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime}
    (kind : actionFamily tick.action = .runtime)
    (prior : OwnershipPrefix runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences processed tick.before) :
    ∃ next : OwnershipPrefix runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after,
      next.custody.caps = prior.custody.caps.retain tick.after.shared ∧
      next.custody.catalogue = prior.custody.catalogue := by
  have entries := runtime_entries namespaces tick.operation kind
  have allocation := fun object => actor_step_allocated lifetimes tick.operation object
  have earlier : ∀ parent name object, tick.after.shared.entries parent name = some object →
      tick.before.shared.entries parent name = some object := by
    intro parent name object bound
    rwa [entries] at bound
  have authorities : RootAuthorities (prior.custody.caps.retain tick.after.shared) tick.after.shared hostUid := by
    intro root member
    have kept := (List.mem_filter.mp member).1
    have bound : tick.after.shared.entries root.parent root.name = some root.object := by
      simpa using (List.mem_filter.mp member).2
    obtain ⟨childInfo, parentInfo, childKnown, parentKnown, owner, mode, directory, trusted⟩ :=
      prior.custody.namespaceState.authorities root kept
    obtain ⟨laterChild, laterChildKnown, sameChild⟩ := heldMetadata.sdk _ _ tick.operation kind
      (.inr (.inl ⟨root.parent, root.name, bound⟩)) childKnown
    obtain ⟨laterParent, laterParentKnown, sameParent⟩ := heldMetadata.sdk _ _ tick.operation kind
      (.inr (.inr ⟨root.name, root.object, bound⟩)) parentKnown
    exact ⟨laterChild, laterParent, laterChildKnown, laterParentKnown, sameChild.1.trans owner,
      (same_authority_mask sameChild 63 (by decide)).trans mode,
      (same_authority_directory sameChild).trans directory, (same_authority_trusted hostUid sameParent).trans trusted⟩
  have privateDirectories : PrivateDirectoryAuthority tick.after.shared prior.custody.caps.family hostUid directories := by
    intro object scope information label known directory
    have alive : ObjectAlive tick.after.shared object := ⟨information, known⟩
    obtain ⟨oldInformation, oldKnown⟩ := actor_step_live_backward_for objects tick.operation
      (prior.custody.namespaceState.graph.live object scope label) alive
    obtain ⟨owner, mode⟩ := prior.custody.namespaceState.privateDirectories object scope oldInformation label oldKnown directory
    obtain ⟨later, laterKnown, same⟩ := metadata.sdk _ _ tick.operation kind alive oldKnown
    have identity := Option.some.inj (known.symm.trans laterKnown)
    subst later
    exact ⟨same.1.trans owner, (same_authority_mask same 63 (by decide)).trans mode⟩
  have state : NamespaceCustody tick.after.shared (prior.custody.caps.retain tick.after.shared) hostUid
      initial.allocated dataObjects directories foreignReferences := by
    refine ⟨retained_capabilities_valid prior.custody.namespaceState.registry allocation,
      family_graph_delete prior.custody.namespaceState.graph allocation earlier,
      root_boundaries_retain prior.custody.namespaceState.boundaries (by
        intro parent name object scope bound label
        exact earlier parent name object bound),
      authorities, privateDirectories, prior.custody.namespaceState.scopes,
      ⟨fun object held => allocation object (prior.custody.namespaceState.foreignSafe.1 object held),
        prior.custody.namespaceState.foreignSafe.2⟩, ?_⟩
    intro parent name object bound
    have old := prior.custody.namespaceState.wellFormed parent name object (earlier parent name object bound)
    exact ⟨allocation parent old.1, allocation object old.2⟩
  have names : RegisteredRootNames (prior.custody.caps.retain tick.after.shared) semantics tick.after.shared := by
    intro root member
    have kept := List.mem_filter.mp member
    have bound : tick.after.shared.entries root.parent root.name = some root.object := by simpa using kept.2
    exact byte_exact_after_lookup_bits (prior.custody.names root kept.1)
      (lookup.sdk _ tick.operation kind (prior.custody.namespaceState.registry.1 root kept.1).2.1
        (.inr (.inr ⟨root.name, root.object, bound⟩)))
  have owned := retained_engine_references_owned prior.custody.consistent
    (runtime_references_from sdk tick.operation kind) (unchanged_existing_labels _ _ _)
    (by intro record member; exact member) prior.custody.references
  let next := prior.custody.advance descriptors lifetimes references (prior.custody.caps.retain tick.after.shared)
    prior.custody.catalogue state names (catalogue_retained_covers prior.custody.coverage)
    (catalogue_advance_valid prior.custody.valid allocation) owned .same
  have ownership : CustodyOwnershipStep prior.custody.catalogue tick prior.custody.caps.family prior.custody.caps.family := by
    constructor
    · intro parent name object scope bound label missing
      exact False.elim (missing (by rwa [entries]))
    · intro object scope allocated label released
      exact False.elim (released label)
  exact ⟨prior.advance next (by intro record member; exact member) ownership, rfl, rfl⟩

-- §FS-host-boundary.ownership: Return/loss of a real source SDK call extends the
-- registered global induction state. Only the parent operation is framed; actual
-- controller/VMM progress remains in its own recorded child rows.
theorem runtime_registered_custody_retained {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    (namespaces : RuntimeNamespaceContract runtime) (sdk : RuntimeDescriptorContract runtime)
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (objects : ObjectLifetimeContract runtime)
    (metadata : LiveMetadataContract runtime child) (heldMetadata : GlobalAuthorityContract runtime child)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {all processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {callers : NativeProcesses}
    (kind : actionFamily tick.action = .runtime)
    (prior : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before callers) :
    ∃ next : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
        foreignReferences (processed ++ [tick]) tick.after callers,
      next.current.source.custody.catalogue = prior.current.source.custody.catalogue ∧
      next.current.source.custody.caps.family = prior.current.source.custody.caps.family := by
  obtain ⟨next, caps, catalogue⟩ := runtime_ownership_prefix namespaces sdk descriptors lifetimes references
    objects metadata heldMetadata lookup kind prior.current.source
  have ownership : CustodyOwnershipStep next.custody.catalogue tick
      prior.current.source.custody.caps.family next.custody.caps.family := by
    rw [caps]
    have entries := runtime_entries namespaces tick.operation kind
    exact nonremoving_ownership_step _ (by intro parent name object bound; rwa [entries])
      (by intro object allocated; rfl)
  refine ⟨prior.sourceStep sdk lifetimes next ?_ ?_ catalogue ownership ?_, catalogue, ?_⟩
  · intro actor handles closeExec directory impossible
    rw [impossible] at kind
    cases kind
  · rw [caps]
    exact unchanged_existing_labels _ _ _
  · exact no_root_use_of_nonfilesystem (by intro filesystem; rw [filesystem] at kind; cases kind)
  · have family := congrArg Capabilities.family caps
    exact family

-- §AR-host-boundary.interfaces: Preserve the original parent SDK-row consumer.
theorem runtime_registered_custody {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    (namespaces : RuntimeNamespaceContract runtime) (sdk : RuntimeDescriptorContract runtime)
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (objects : ObjectLifetimeContract runtime)
    (metadata : LiveMetadataContract runtime child) (heldMetadata : GlobalAuthorityContract runtime child)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {all processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {callers : NativeProcesses}
    (kind : actionFamily tick.action = .runtime)
    (prior : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before callers) :
    Nonempty (RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after callers) := by
  obtain ⟨next, catalogue, family⟩ := runtime_registered_custody_retained namespaces sdk descriptors lifetimes
    references objects metadata heldMetadata lookup kind prior
  exact ⟨next⟩

end LeanCage.Host.Kernel
