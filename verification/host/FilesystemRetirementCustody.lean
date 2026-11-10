import FilesystemCustodyState
import FilesystemNativeRetirement

namespace LeanCage.Host.Kernel
open Filesystem

variable {sourceProgram : Program UInt32}

-- §AR-host-boundary.primitives: Kernel exit drops references and live metadata, not stored
-- positive directory bindings. Every remaining shared field still follows its own row law.
theorem retirement_entries {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (laws : RetirementContract runtime) {before after : Population} {action : ActorAction}
    (actual : ActorStep runtime action before after) (kind : actionFamily action = .retirement) :
    after.shared.entries = before.shared.entries := by
  cases actual with
  | launch => cases kind
  | @returned β population actor engine effect next reply world present alive head operation => cases effect <;> cases kind
  | @lost β population actor engine effect next world present alive head operation => cases effect <;> cases kind
  | foreign => cases kind
  | retire present operation =>
    have same := laws.engine_entries _ _ _ _ _ operation
    exact same
  | nativeRetire operation => exact laws.native_entries _ _ _ _ _ _ operation

theorem retirement_references_from {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (laws : RetirementContract runtime) {before after : Population} {action : ActorAction}
    (actual : ActorStep runtime action before after) (kind : actionFamily action = .retirement) :
    EngineReferencesFrom before after := by
  cases actual with
  | launch => cases kind
  | @returned β population actor engine effect next reply world present alive head operation => cases effect <;> cases kind
  | @lost β population actor engine effect next world present alive head operation => cases effect <;> cases kind
  | foreign => cases kind
  | @retire population owner current observation world ownerPresent operation =>
    intro actor engine present fd handle held
    by_cases same : actor = owner
    · subst actor
      simp only [Population.advance, Population.install, ite_eq_left] at present
      have identity := Option.some.inj present
      subst engine
      exact ⟨current, ownerPresent, laws.engine_subset _ _ _ _ _ _ _ operation held⟩
    · exact ⟨engine, by simpa only [Population.advance, Population.install, ite_eq_right same] using present, held⟩
  | nativeRetire operation => exact fun actor engine present fd handle held => ⟨engine, present, held⟩

-- §FS-host-boundary.ownership: Actual teardown retains old birth/catalogue ownership while
-- allowing the final unlinked inode's metadata and every released handle to disappear.
theorem retirement_ownership_prefix {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    (retirement : RetirementContract runtime) (descriptors : DescriptorContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (objects : ObjectLifetimeContract runtime) (metadata : LiveMetadataContract runtime child)
    (heldMetadata : GlobalAuthorityContract runtime child)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {ticks processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime}
    (kind : actionFamily tick.action = .retirement)
    (prior : OwnershipPrefix runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences processed tick.before) :
    ∃ next : OwnershipPrefix runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after,
      next.custody.caps = prior.custody.caps.retain tick.after.shared ∧
      next.custody.catalogue = prior.custody.catalogue := by
  have entries := retirement_entries retirement tick.operation kind
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
    obtain ⟨laterChild, laterChildKnown, sameChild⟩ := heldMetadata.retirement _ _ tick.operation kind
      (.inr (.inl ⟨root.parent, root.name, bound⟩)) childKnown
    obtain ⟨laterParent, laterParentKnown, sameParent⟩ := heldMetadata.retirement _ _ tick.operation kind
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
    obtain ⟨later, laterKnown, same⟩ := metadata.retirement _ _ tick.operation kind alive oldKnown
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
      (lookup.retirement _ tick.operation kind (prior.custody.namespaceState.registry.1 root kept.1).2.1
        (.inr (.inr ⟨root.name, root.object, bound⟩)))
  have owned := retained_engine_references_owned prior.custody.consistent
    (retirement_references_from retirement tick.operation kind) (unchanged_existing_labels _ _ _)
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

theorem retirement_custody_state_retained {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    (runtimeLaws : RuntimeDescriptorContract runtime) (descriptors : DescriptorContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (objects : ObjectLifetimeContract runtime) (metadata : LiveMetadataContract runtime child)
    (heldMetadata : GlobalAuthorityContract runtime child)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {ticks processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {callers : NativeProcesses}
    (kind : actionFamily tick.action = .retirement)
    (prior : CustodyState runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences processed tick.before callers) :
    ∃ next : CustodyState runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after callers,
      next.source.custody.catalogue = prior.source.custody.catalogue ∧
      next.source.custody.caps.family = prior.source.custody.caps.family := by
  obtain ⟨next, caps, catalogue⟩ := retirement_ownership_prefix runtimeLaws.toRetirementContract descriptors lifetimes
    references objects metadata heldMetadata lookup kind prior.source
  have ownership : CustodyOwnershipStep next.custody.catalogue tick
      prior.source.custody.caps.family next.custody.caps.family := by
    rw [caps]
    have entries := retirement_entries runtimeLaws.toRetirementContract tick.operation kind
    constructor
    · intro parent name object scope bound label missing
      exact False.elim (missing (by rwa [entries]))
    · intro object scope allocated label released
      exact False.elim (released label)
  refine ⟨prior.application runtimeLaws lifetimes next ?_ ?_ ?_ ?_ ownership, catalogue, ?_⟩
  · intro actor owned closeExec directory impossible
    rw [impossible] at kind
    cases kind
  · rw [caps]
    exact unchanged_existing_labels _ _ _
  · rw [catalogue]
    exact fun _ member => member
  · rw [catalogue]
    exact fun _ member => .inl member
  · have family := congrArg Capabilities.family caps
    exact family

-- §AR-host-boundary.interfaces: Preserve the original actual-retirement catalogue projection.
theorem retirement_custody_state_catalogued {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    (runtimeLaws : RuntimeDescriptorContract runtime) (descriptors : DescriptorContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (objects : ObjectLifetimeContract runtime) (metadata : LiveMetadataContract runtime child)
    (heldMetadata : GlobalAuthorityContract runtime child)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {ticks processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {callers : NativeProcesses}
    (kind : actionFamily tick.action = .retirement)
    (prior : CustodyState runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences processed tick.before callers) :
    ∃ next : CustodyState runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after callers,
      next.source.custody.catalogue = prior.source.custody.catalogue := by
  obtain ⟨next, catalogue, family⟩ := retirement_custody_state_retained runtimeLaws descriptors lifetimes references
    objects metadata heldMetadata lookup kind prior
  exact ⟨next, catalogue⟩

private theorem retirement_custody_base {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    (runtimeLaws : RuntimeDescriptorContract runtime) (descriptors : DescriptorContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (objects : ObjectLifetimeContract runtime) (metadata : LiveMetadataContract runtime child)
    (heldMetadata : GlobalAuthorityContract runtime child)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {ticks processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {callers : NativeProcesses}
    (kind : actionFamily tick.action = .retirement)
    (prior : CustodyState runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences processed tick.before callers) :
    Nonempty (CustodyState runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after callers) := by
  obtain ⟨next, _⟩ := retirement_custody_state_catalogued runtimeLaws descriptors lifetimes references objects metadata
    heldMetadata lookup kind prior
  exact ⟨next⟩

-- §FS-host-boundary.ownership: The actual engine retirement extends the common family,
-- birth, native-reference and removal histories; it does not manufacture a cleanup result.
theorem engine_retirement_custody_state {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    (runtimeLaws : RuntimeDescriptorContract runtime) (descriptors : DescriptorContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (objects : ObjectLifetimeContract runtime) (metadata : LiveMetadataContract runtime child)
    (heldMetadata : GlobalAuthorityContract runtime child)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {ticks processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {callers : NativeProcesses}
    {actor : ActorId} {observation : EngineRetirement} (action : tick.action = .retire actor observation)
    (prior : CustodyState runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences processed tick.before callers) :
    Nonempty (CustodyState runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after callers) :=
  retirement_custody_base runtimeLaws descriptors lifetimes references objects metadata heldMetadata lookup
    (by rw [action]; rfl) prior

-- §FS-host-boundary.ownership: The Python caller's SAME observed exit updates its native
-- ledger as well. Partial surviving resources retain their earlier private/public provenance.
theorem native_retirement_custody_state {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    (runtimeLaws : RuntimeDescriptorContract runtime) (descriptors : DescriptorContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (objects : ObjectLifetimeContract runtime) (metadata : LiveMetadataContract runtime child)
    (heldMetadata : GlobalAuthorityContract runtime child)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {ticks processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {before after : NativeProcesses}
    (exit : NativeRetirementAt tick before after)
    (prior : CustodyState runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences processed tick.before before) :
    Nonempty (CustodyState runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after after) := by
  obtain ⟨base⟩ := retirement_custody_base runtimeLaws descriptors lifetimes references objects metadata heldMetadata lookup
    (by rw [exit.action]; rfl) prior
  exact ⟨{
    source := base.source
    nativePublic := fun object held => base.nativePublic object
      (native_retirement_held_before runtimeLaws.toRetirementContract exit held)
    nativeLive := fun object held => base.nativeLive object
      (native_retirement_held_before runtimeLaws.toRetirementContract exit held)
    directoriesPublic := base.directoriesPublic
    directoriesLive := base.directoriesLive
    births := base.births }⟩

end LeanCage.Host.Kernel
