import FilesystemNativeNamespace
import FilesystemBoundaryAuthority
import FilesystemBoundaryComparison
import FilesystemOwnershipPrefix

namespace LeanCage.Host.Kernel
open Filesystem

variable {sourceProgram : Program UInt32}

-- §AR-host-boundary.primitives: The metadata law applies only to an old lifetime still
-- alive after ONE native call. Only that exact setter's actual target may change authority.
structure NativeLiveMetadataContract {kernel : Contract} (primitive : NativePrimitive kernel) : Prop where
  existing : ∀ {program : Program UInt32} {runtime : ActorRuntime kernel program}
    {before after : NativeProcesses} {tick : ActorTick runtime}
    (call : NativeCallAt primitive tick before after) object information,
    ObjectAlive tick.after.shared object → tick.before.shared.information object = some information →
    ∃ later, tick.after.shared.information object = some later ∧
      (SameAuthority information later ∨ NativeCallAuthorityTarget call object)
  bound_live : ∀ {program : Program UInt32} {runtime : ActorRuntime kernel program}
    {before after : NativeProcesses} {tick : ActorTick runtime}
    (_call : NativeCallAt primitive tick before after) parent name object,
    tick.after.shared.entries parent name = some object →
    ObjectAlive tick.after.shared parent ∧ ObjectAlive tick.after.shared object

private theorem foreign_actual {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {before after : Population} {caller : Credentials}
    (actual : ActorStep runtime (.foreign caller) before after) : runtime.foreign caller before.shared after.shared := by
  cases actual
  assumption

private theorem foreign_actors {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {before after : Population} {caller : Credentials}
    (actual : ActorStep runtime (.foreign caller) before after) : after.actors = before.actors := by
  cases actual
  rfl

theorem native_private_authority {kernel : Contract} {primitive : NativePrimitive kernel}
    (namespaceLaws : NativeNamespaceContract primitive) (metadata : NativeLiveMetadataContract primitive)
    {runtime : ActorRuntime kernel sourceProgram} {before after : NativeProcesses} {tick : ActorTick runtime}
    {family : Family} (call : NativeCallAt primitive tick before after)
    (profile : NativePrivateOperandProfile namespaceLaws call family) (safe : NativeReferencesPublic before family)
    {object scope : ObjectId} {information : Stat} (privateObject : family object = some scope)
    (alive : ObjectAlive tick.after.shared object) (known : tick.before.shared.information object = some information) :
    ∃ later, tick.after.shared.information object = some later ∧ SameAuthority information later := by
  obtain ⟨later, current, same | target⟩ := metadata.existing call object information alive known
  · exact ⟨later, current, same⟩
  · have publicObject := native_authority_target_public namespaceLaws call profile safe target
    rw [privateObject] at publicObject
    cases publicObject

-- §FS-host-boundary.ownership: Actual resolved native operands and the existing external
-- host-code profile preserve custody. The conclusion is derived, never a callback end-frame.
theorem native_custody_prefix_current {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {primitive : NativePrimitive kernel} {hostUid : Nat} {semantics : NameSemanticsView}
    {dataObjects directories : ObjectId → Prop}
    (namespaceLaws : NativeNamespaceContract primitive) (metadata : NativeLiveMetadataContract primitive)
    (heldMetadata : NativeMetadataContract primitive) (descriptors : DescriptorContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (objects : ObjectLifetimeContract runtime) (lookup : NativeNonemptyLookupContract primitive semantics)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    (boundaryProfile : NativeBoundaryAuthorityProfile primitive ticks hostUid)
    {position : Nat} {tick : ActorTick runtime} (selected : ticks[position]? = some tick)
    {before after : NativeProcesses} (call : NativeCallAt primitive tick before after)
    {processed : List (ActorTick runtime)} {foreignReferences : ForeignReferences}
    (prior : OwnershipPrefix runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences processed tick.before)
    (profile : NativePrivateOperandProfile namespaceLaws call prior.custody.caps.family)
    (nativePublic : NativeReferencesPublic before prior.custody.caps.family) :
    ∃ next : OwnershipPrefix runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after,
      NativeReferencesPublic after next.custody.caps.family ∧ NativeReferencesLive after tick.after.shared ∧
      next.custody.caps = prior.custody.caps.retain tick.after.shared ∧
      next.custody.catalogue = prior.custody.catalogue := by
  have allocation : ∀ object, tick.before.shared.allocated object = true → tick.after.shared.allocated object = true :=
    fun object => actor_step_allocated lifetimes tick.operation object
  have foreignOperation : runtime.foreign call.caller tick.before.shared tick.after.shared :=
    foreign_actual (call.action ▸ tick.operation)
  have earlier : ∀ parent name object scope, tick.after.shared.entries parent name = some object →
      prior.custody.caps.family object = some scope → tick.before.shared.entries parent name = some object :=
    fun _ _ _ _ bound label => native_private_binding_earlier namespaceLaws call profile
      prior.custody.namespaceState.graph nativePublic bound label
  have privateDirectories : PrivateDirectoryAuthority tick.after.shared prior.custody.caps.family hostUid directories := by
    intro object scope information label known directory
    have alive : ObjectAlive tick.after.shared object := ⟨information, known⟩
    obtain ⟨oldInformation, oldKnown⟩ := objects.foreign _ _ _ _ foreignOperation
      (prior.custody.namespaceState.graph.live object scope label) alive
    obtain ⟨owner, mode⟩ := prior.custody.namespaceState.privateDirectories object scope oldInformation label oldKnown directory
    obtain ⟨later, laterKnown, same⟩ := native_private_authority namespaceLaws metadata call profile nativePublic
      label alive oldKnown
    have informationSame := Option.some.inj (known.symm.trans laterKnown)
    subst later
    exact ⟨same.1.trans owner, (same_authority_mask same 63 (by decide)).trans mode⟩
  have authorities : RootAuthorities (prior.custody.caps.retain tick.after.shared) tick.after.shared hostUid := by
    intro root kept
    have member := (List.mem_filter.mp kept).1
    have binding := native_private_binding_preserved namespaceLaws call profile
      (prior.custody.namespaceState.registry.1 root member).2.2.1
      (prior.custody.namespaceState.registry.1 root member).2.2.2.1
    obtain ⟨childInfo, parentInfo, childKnown, parentKnown, owner, mode, directory, trusted⟩ :=
      prior.custody.namespaceState.authorities root member
    obtain ⟨laterChild, laterChildKnown, childSame⟩ := native_private_authority namespaceLaws metadata call profile
      nativePublic (prior.custody.namespaceState.registry.1 root member).2.2.2.1
      (metadata.bound_live call root.parent root.name root.object binding).2 childKnown
    obtain ⟨lease⟩ := actual_boundary_parent_lease lifetimes journal selected prior.custody.catalogue
      prior.custody.coverage prior.custody.namespaceState.registry prior.custody.namespaceState.authorities member
    have parentHeld : GloballyHeld tick.after root.parent := .inr (.inr ⟨root.name, root.object, binding⟩)
    obtain ⟨laterParent, laterParentKnown, parentSame⟩ :=
      native_boundary_parent_authority heldMetadata boundaryProfile selected call lease parentHeld parentKnown
    exact ⟨laterChild, laterParent, laterChildKnown, laterParentKnown, childSame.1.trans owner,
      (same_authority_mask childSame 63 (by decide)).trans mode, (same_authority_directory childSame).trans directory,
      (same_authority_trusted hostUid parentSame).trans trusted⟩
  have state : NamespaceCustody tick.after.shared (prior.custody.caps.retain tick.after.shared) hostUid
      initial.allocated dataObjects directories foreignReferences :=
    ⟨retained_capabilities_valid prior.custody.namespaceState.registry allocation,
      native_namespace_family namespaceLaws lifetimes call profile prior.custody.namespaceState.graph nativePublic,
      root_boundaries_retain prior.custody.namespaceState.boundaries earlier, authorities, privateDirectories,
      prior.custody.namespaceState.scopes,
      ⟨fun object held => allocation object (prior.custody.namespaceState.foreignSafe.1 object held),
        prior.custody.namespaceState.foreignSafe.2⟩,
      native_namespace_well_formed namespaceLaws lifetimes call prior.custody.namespaceState.wellFormed⟩
  have names := native_registered_root_names lookup call prior.custody.namespaceState.registry prior.custody.names
  have actors := foreign_actors (call.action ▸ tick.operation)
  have owned : EngineReferencesOwned runtime ticks tick.after prior.custody.caps.family prior.custody.catalogue := by
    intro actor engine present fd handle scope live label
    rw [actors] at present
    exact prior.custody.references actor engine present fd handle scope live label
  let next := prior.custody.advance descriptors lifetimes references (prior.custody.caps.retain tick.after.shared)
    prior.custody.catalogue state names (catalogue_retained_covers prior.custody.coverage)
    (catalogue_advance_valid prior.custody.valid allocation) owned .same
  exact ⟨prior.advance next (by intro record member; exact member)
      (native_namespace_ownership_step namespaceLaws prior.custody.catalogue call profile),
    native_references_public namespaceLaws call profile prior.custody.namespaceState.graph nativePublic,
    namespaceLaws.references_live call, rfl, rfl⟩

-- §AR-host-boundary.interfaces: Retain the existing native consumer; the current sibling
-- additionally keeps the exact next catalogue/capabilities for CWD and joint-ledger composition.
theorem native_custody_prefix {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {primitive : NativePrimitive kernel} {hostUid : Nat} {semantics : NameSemanticsView}
    {dataObjects directories : ObjectId → Prop}
    (namespaceLaws : NativeNamespaceContract primitive) (metadata : NativeLiveMetadataContract primitive)
    (heldMetadata : NativeMetadataContract primitive) (descriptors : DescriptorContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (objects : ObjectLifetimeContract runtime) (lookup : NativeNonemptyLookupContract primitive semantics)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    (boundaryProfile : NativeBoundaryAuthorityProfile primitive ticks hostUid)
    {position : Nat} {tick : ActorTick runtime} (selected : ticks[position]? = some tick)
    {before after : NativeProcesses} (call : NativeCallAt primitive tick before after)
    {processed : List (ActorTick runtime)} {foreignReferences : ForeignReferences}
    (prior : OwnershipPrefix runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences processed tick.before)
    (profile : NativePrivateOperandProfile namespaceLaws call prior.custody.caps.family)
    (nativePublic : NativeReferencesPublic before prior.custody.caps.family) :
    ∃ next : OwnershipPrefix runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after,
      NativeReferencesPublic after next.custody.caps.family ∧ NativeReferencesLive after tick.after.shared := by
  obtain ⟨next, publicReferences, liveReferences, caps, catalogue⟩ :=
    native_custody_prefix_current namespaceLaws metadata heldMetadata descriptors lifetimes references objects lookup
      journal boundaryProfile selected call prior profile nativePublic
  exact ⟨next, publicReferences, liveReferences⟩

end LeanCage.Host.Kernel
