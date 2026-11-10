import FilesystemRegisteredCustody

namespace LeanCage.Host.Kernel
open Filesystem

variable {sourceProgram : Program UInt32}

-- §AR-host-boundary.interfaces: Reuse the existing per-operation metadata law
-- across source interpreters; every runtime relation is definitionally identical.
def ActorRuntime.logicalView {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram) : ActorRuntime kernel :=
  ⟨runtime.other, runtime.foreign, runtime.initialReferences, runtime.retire, runtime.nativeRetire⟩

private theorem foreign_actual {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {caller : Credentials} {before after : Population}
    (actual : ActorStep runtime (.foreign caller) before after) : runtime.foreign caller before.shared after.shared := by
  cases actual
  assumption

private theorem foreign_actors {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {caller : Credentials} {before after : Population}
    (actual : ActorStep runtime (.foreign caller) before after) : after.actors = before.actors := by
  cases actual
  rfl

-- §FS-host-boundary.ownership: Derive denial from this real removal's metadata
-- and Linux permission checks. Public data/name interference remains unrestricted.
theorem ordinary_private_binding_preserved {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (foreign : ForeignContract runtime) {hostUid : Nat} {caller : Credentials}
    {before after : World} {caps : Capabilities} {initialObjects : ObjectId → Bool}
    {dataObjects directories : ObjectId → Prop} {references : ForeignReferences}
    (actual : runtime.foreign caller before after) (allowed : OrdinaryForeign caller hostUid)
    (directoryParents : ∀ parent name object, before.entries parent name = some object → directories parent)
    (state : NamespaceCustody before caps hostUid initialObjects dataObjects directories references)
    {parent object scope : ObjectId} {name : ByteArray}
    (bound : before.entries parent name = some object) (label : caps.family object = some scope) :
    after.entries parent name = some object := by
  apply Classical.byContradiction
  intro removed
  obtain ⟨parentInfo, childInfo, parentKnown, childKnown, permission⟩ :=
    foreign.remove_permission caller before after parent name object actual bound removed
  cases parentLabel : caps.family parent with
  | none =>
    obtain ⟨knownParent, knownChild, first, second, trusted, owner⟩ :=
      root_boundaries_authority state.boundaries state.authorities parent name object scope bound label parentLabel
    have sameParent := Option.some.inj (parentKnown.symm.trans first)
    have sameChild := Option.some.inj (childKnown.symm.trans second)
    subst knownParent
    subst knownChild
    exact trusted_parent_no_remove caller hostUid parentInfo childInfo allowed.1 allowed.2.1 allowed.2.2.1
      allowed.2.2.2 trusted owner permission
  | some parentScope =>
    obtain ⟨owner, mode⟩ := state.privateDirectories parent parentScope parentInfo parentLabel parentKnown
      (directoryParents parent name object bound)
    exact masked_no_search caller parentInfo (by rw [owner]; exact allowed.1) allowed.2.2.1 mode permission.2.1

-- §FS-host-boundary.lookup: A still-bound trusted parent retains its comparison
-- rules by the individual authority check; foreign-owned public input flags may change.
theorem ordinary_registered_root_names {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {tick : ActorTick runtime} {caller : Credentials} (action : tick.action = .foreign caller)
    (allowed : OrdinaryForeign caller hostUid) {caps : Capabilities} {semantics : NameSemanticsView}
    (valid : caps.Valid tick.before.shared) (authorities : RootAuthorities caps tick.before.shared hostUid)
    (names : RegisteredRootNames caps semantics tick.before.shared) :
    RegisteredRootNames (caps.retain tick.after.shared) semantics tick.after.shared := by
  intro root member
  have kept := List.mem_filter.mp member
  have bound : tick.after.shared.entries root.parent root.name = some root.object := by simpa using kept.2
  obtain ⟨childInfo, parentInfo, childKnown, parentKnown, owner, mode, directory, trusted⟩ := authorities root kept.1
  have owners : parentInfo.uid = hostUid ∨ parentInfo.uid = 0 := by
    simp only [Directories.trusted, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at trusted
    exact trusted.1.2
  have held : GloballyHeld tick.after root.parent := .inr (.inr ⟨root.name, root.object, bound⟩)
  have bits : LookupBitsEqual tick.before.shared tick.after.shared root.parent := by
    rcases lookup.ordinary root.parent parentInfo (action ▸ tick.operation) (valid.1 root kept.1).2.1 held parentKnown with same | changed
    · exact same
    · rcases changed with same | bypass
      · rcases owners with host | rootOwner
        · exact False.elim (allowed.1 (same.trans host))
        · exact False.elim (allowed.2.1 (same.trans rootOwner))
      · rw [allowed.2.2.2] at bypass
        cases bypass
  exact byte_exact_after_lookup_bits (names root kept.1) bits

-- §FS-host-boundary.ownership: This exact ordinary-foreign row advances the full
-- registered custody state and foreign capability pool. It grants no application
-- or host-account callback role to an unrelated foreign process.
theorem ordinary_registered_custody_retained {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {semantics : NameSemanticsView} {dataObjects directories : ObjectId → Prop}
    (foreign : ForeignContract runtime) (authority : ForeignAuthorityContract runtime.logicalView)
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (sdk : RuntimeDescriptorContract runtime)
    (objects : ObjectLifetimeContract runtime) (metadata : LiveMetadataContract runtime child)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {all processed : List (ActorTick runtime)} {tick : ActorTick runtime}
    {first last : Processes} (recorded : process.step tick first last) {caller : Credentials}
    (action : tick.action = .foreign caller) (allowed : OrdinaryForeign caller hostUid)
    {foreignBefore foreignAfter : ForeignReferences} {callers : NativeProcesses}
    (view : DirectoryView tick.before.shared directories)
    (directoryParents : ∀ parent name object, tick.before.shared.entries parent name = some object → directories parent)
    (observed : ForeignNamespaceObservation tick.before.shared tick.after.shared foreignBefore foreignAfter
      initial.allocated directories caller)
    (prior : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignBefore processed tick.before callers) :
    ∃ next : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
        foreignAfter (processed ++ [tick]) tick.after callers,
      next.current.source.custody.catalogue = prior.current.source.custody.catalogue ∧
      next.current.source.custody.caps.family = prior.current.source.custody.caps.family := by
  have actual := foreign_actual (action ▸ tick.operation)
  let previous := prior.current.source.custody.namespaceState
  have allocation := fun object => actor_step_allocated lifetimes tick.operation object
  have boundary : PrivateBoundaryAuthority tick.before.shared prior.current.source.custody.caps.family hostUid :=
    root_boundaries_authority previous.boundaries previous.authorities
  have earlier : ∀ parent name object scope, tick.after.shared.entries parent name = some object →
      prior.current.source.custody.caps.family object = some scope → tick.before.shared.entries parent name = some object :=
    fun _ _ _ _ bound label => foreign_private_binding_earlier previous.graph view previous.privateDirectories
      boundary previous.foreignSafe allowed observed bound label
  have state : NamespaceCustody tick.after.shared (prior.current.source.custody.caps.retain tick.after.shared) hostUid
      initial.allocated dataObjects directories foreignAfter := by
    refine ⟨retained_capabilities_valid previous.registry allocation,
      foreign_namespace_family previous.graph view previous.privateDirectories
        boundary previous.foreignSafe allowed observed allocation,
      root_boundaries_retain previous.boundaries earlier, ?_, ?_, previous.scopes,
      foreign_namespace_references previous.graph view previous.privateDirectories previous.scopes previous.foreignSafe
        allowed observed, foreign_namespace_well_formed observed previous.wellFormed allocation⟩
    · intro root member
      have old := (List.mem_filter.mp member).1
      let foreignView : ForeignContract runtime.logicalView := ⟨foreign.remove_permission, foreign.attribute_permission⟩
      have bound := ordinary_foreign_preserves_root foreignView actual allowed previous.registry previous.authorities root old
      exact foreign_root_authority_after authority actual allowed (previous.authorities root old)
        bound
    · intro object scope information label known directory
      have alive : ObjectAlive tick.after.shared object := ⟨information, known⟩
      obtain ⟨earlierInfo, earlierKnown⟩ := actor_step_live_backward_for objects tick.operation
        (previous.graph.live object scope label) alive
      obtain ⟨owner, mask⟩ := previous.privateDirectories object scope earlierInfo label earlierKnown directory
      let source : ExternalStep process child hostUid first tick last := .ordinary caller recorded action allowed
      have safe : ExternalAuthoritySafe source := by simp only [source, ExternalAuthoritySafe]
      obtain ⟨laterInfo, laterKnown, same⟩ := external_step_live_authority_for metadata source
        safe earlierKnown (.inl owner) alive
      have identity := Option.some.inj (known.symm.trans laterKnown)
      subst laterInfo
      exact ⟨same.1.trans owner, (same_authority_mask same 63 (by decide)).trans mask⟩
  have names := ordinary_registered_root_names lookup action allowed prior.current.source.custody.namespaceState.registry
    prior.current.source.custody.namespaceState.authorities prior.current.source.custody.names
  have actors := foreign_actors (action ▸ tick.operation)
  have owned : EngineReferencesOwned runtime all tick.after prior.current.source.custody.caps.family
      prior.current.source.custody.catalogue := by
    intro actor engine present fd handle scope live label
    rw [actors] at present
    exact prior.current.source.custody.references actor engine present fd handle scope live label
  let next := prior.current.source.custody.advance descriptors lifetimes references
    (prior.current.source.custody.caps.retain tick.after.shared) prior.current.source.custody.catalogue
    state names (catalogue_retained_covers prior.current.source.custody.coverage)
    (catalogue_advance_valid prior.current.source.custody.valid
      (fun object => actor_step_allocated lifetimes tick.operation object)) owned .same
  have ownership : CustodyOwnershipStep next.catalogue tick prior.current.source.custody.caps.family next.caps.family := by
    constructor
    · intro parent name object scope bound label missing
      exact False.elim (missing (ordinary_private_binding_preserved foreign actual allowed directoryParents
        prior.current.source.custody.namespaceState bound label))
    · intro object scope allocated label released
      exact False.elim (released label)
  let afterSource := prior.current.source.advance next (by intro record member; exact member) ownership
  refine ⟨prior.sourceStep sdk lifetimes afterSource ?_ (unchanged_existing_labels _ _ _) rfl ownership ?_, rfl, rfl⟩
  · intro actor handles closeExec directory impossible
    rw [action] at impossible
    cases impossible
  · exact no_root_use_of_nonfilesystem (by rw [action]; intro impossible; cases impossible)

-- §AR-host-boundary.interfaces: Preserve the original ordinary-row result;
-- the cumulative publication fold consumes the stronger exact retained-family sibling.
theorem ordinary_registered_custody {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {semantics : NameSemanticsView} {dataObjects directories : ObjectId → Prop}
    (foreign : ForeignContract runtime) (authority : ForeignAuthorityContract runtime.logicalView)
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (sdk : RuntimeDescriptorContract runtime)
    (objects : ObjectLifetimeContract runtime) (metadata : LiveMetadataContract runtime child)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {all processed : List (ActorTick runtime)} {tick : ActorTick runtime}
    {first last : Processes} (recorded : process.step tick first last) {caller : Credentials}
    (action : tick.action = .foreign caller) (allowed : OrdinaryForeign caller hostUid)
    {foreignBefore foreignAfter : ForeignReferences} {callers : NativeProcesses}
    (view : DirectoryView tick.before.shared directories)
    (directoryParents : ∀ parent name object, tick.before.shared.entries parent name = some object → directories parent)
    (observed : ForeignNamespaceObservation tick.before.shared tick.after.shared foreignBefore foreignAfter
      initial.allocated directories caller)
    (prior : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignBefore processed tick.before callers) :
    Nonempty (RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignAfter (processed ++ [tick]) tick.after callers) := by
  obtain ⟨next, catalogue, family⟩ := ordinary_registered_custody_retained foreign authority descriptors lifetimes
    references sdk objects metadata lookup recorded action allowed view directoryParents observed prior
  exact ⟨next⟩

end LeanCage.Host.Kernel
