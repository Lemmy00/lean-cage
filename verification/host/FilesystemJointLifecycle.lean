import FilesystemPublicationLifecycle
import FilesystemOwnershipRetention

namespace LeanCage.Host.Kernel
open Filesystem

private theorem retained_joint {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignBefore foreignAfter : ForeignReferences} {tick : ActorTick runtime} {before after : NativeProcesses}
    (prior : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignBefore processed tick.before before) (joint : JointPublicationPrefix prior)
    (custody : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignAfter (processed ++ [tick]) tick.after after)
    (catalogue : custody.current.source.custody.catalogue = prior.custody.current.source.custody.catalogue)
    (family : custody.current.source.custody.caps.family = prior.custody.current.source.custody.caps.family)
    (ownership : CustodyOwnershipStep custody.current.source.custody.catalogue tick
      prior.custody.current.source.custody.caps.family custody.current.source.custody.caps.family) :
    ∃ next : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
        foreignAfter (processed ++ [tick]) tick.after after, JointPublicationPrefix next := by
  let next := prior.preserved custody catalogue (by intro object allocated; exact congrFun family object)
  refine ⟨next, joint.advance next ?_ ?_⟩
  · change ∀ record ∈ prior.custody.current.source.custody.catalogue, record ∈ custody.current.source.custody.catalogue
    rw [catalogue]
    exact fun _ member => member
  · refine ⟨ownership, ?_⟩
    change ExistingLabels tick.before.shared tick.after.shared prior.custody.current.source.custody.caps.family
      custody.current.source.custody.caps.family
    rw [family]
    exact unchanged_existing_labels _ _ _

private theorem foreign_actual {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {caller : Credentials} {before after : Population} (source : ActorStep runtime (.foreign caller) before after) :
    runtime.foreign caller before.shared after.shared := by cases source; assumption

private theorem launch_entries {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {before after : Population} {actor : ActorId} {references : UInt64 → Option Handle}
    {closeExec : UInt64 → Bool} {directory : ObjectId}
    (actual : ActorStep runtime (.launch actor references closeExec directory) before after) :
    after.shared.entries = before.shared.entries := by
  cases actual
  rfl

-- §FS-host-boundary.ownership: This actual row retains its exact joint ownership/label history.
theorem runtime_registered_publication_joint {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
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
    (prior : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before callers) (joint : JointPublicationPrefix prior) :
    ∃ next : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after callers, JointPublicationPrefix next := by
  obtain ⟨next, catalogue, family⟩ := runtime_registered_custody_retained namespaces sdk descriptors lifetimes references
    objects metadata heldMetadata lookup kind prior.custody
  apply retained_joint prior joint next catalogue family
  rw [catalogue, family]
  have entries := runtime_entries namespaces tick.operation kind
  exact nonremoving_ownership_step _ (by intro parent name object bound; rwa [entries])
    (by intro object allocated; rfl)

-- §FS-host-boundary.ownership: This actual row retains its exact joint ownership/label history.
theorem ordinary_registered_publication_joint {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
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
    (prior : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignBefore processed tick.before callers) (joint : JointPublicationPrefix prior) :
    ∃ next : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignAfter (processed ++ [tick]) tick.after callers, JointPublicationPrefix next := by
  obtain ⟨next, catalogue, family⟩ := ordinary_registered_custody_retained foreign authority descriptors lifetimes references
    sdk objects metadata lookup recorded action allowed view directoryParents observed prior.custody
  apply retained_joint prior joint next catalogue family
  rw [catalogue, family]
  constructor
  · intro parent name object scope bound label removed
    exact False.elim (removed (ordinary_private_binding_preserved foreign (foreign_actual (action ▸ tick.operation))
      allowed directoryParents prior.custody.current.source.custody.namespaceState bound label))
  · intro object scope allocated label released
    exact False.elim (released label)

-- §FS-host-boundary.ownership: This actual row retains its exact joint ownership/label history.
theorem native_registered_publication_joint {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {primitive : NativePrimitive kernel} {hostUid : Nat} {semantics : NameSemanticsView}
    {dataObjects directories : ObjectId → Prop}
    (namespaceLaws : NativeNamespaceContract primitive) (metadata : NativeLiveMetadataContract primitive)
    (heldMetadata : NativeMetadataContract primitive) (descriptors : DescriptorContract kernel)
    (sdk : RuntimeDescriptorContract runtime) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (objects : ObjectLifetimeContract runtime)
    (lookup : NativeNonemptyLookupContract primitive semantics)
    {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    (boundaryProfile : NativeBoundaryAuthorityProfile primitive all hostUid)
    {position : Nat} {tick : ActorTick runtime} (selected : all[position]? = some tick)
    {before after : NativeProcesses} (call : NativeCallAt primitive tick before after)
    {processed : List (ActorTick runtime)} {foreignReferences : ForeignReferences}
    (prior : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before before)
    (profile : NativePrivateOperandProfile namespaceLaws call prior.custody.current.source.custody.caps.family) (joint : JointPublicationPrefix prior) :
    ∃ next : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after after, JointPublicationPrefix next := by
  obtain ⟨next, catalogue, family⟩ := native_custody_state_retained namespaceLaws metadata heldMetadata descriptors sdk
    lifetimes references objects lookup journal boundaryProfile selected call prior.custody.current profile
  let registered := prior.custody.other next
    (no_root_use_of_nonfilesystem (by rw [call.action]; intro impossible; cases impossible)) catalogue
  apply retained_joint prior joint registered catalogue family
  change CustodyOwnershipStep next.source.custody.catalogue tick prior.custody.current.source.custody.caps.family
    next.source.custody.caps.family
  rw [catalogue, family]
  exact native_namespace_ownership_step namespaceLaws _ call profile

-- §FS-host-boundary.ownership: This actual row retains its exact joint ownership/label history.
theorem handoff_registered_publication_joint {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime)
    {initial : World} {all processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories ipc : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {before : NativeProcesses}
    (handoff : NativeHandoffAt tick before)
    (binding : InitialEngineBinding ipc handoff.execution.references.rawProjection.handles
      handoff.execution.references.rawProjection.closeOnExec)
    (separate : ∀ object, ipc object → ¬ dataObjects object)
    (prior : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before before) (joint : JointPublicationPrefix prior) :
    ∃ next : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after (before.transfer handoff.actor handoff.execution), JointPublicationPrefix next := by
  obtain ⟨next, catalogue, family⟩ := handoff_custody_state_retained descriptors lifetimes references handoff binding separate
    prior.custody.current
  let registered := prior.custody.other next
    (no_root_use_of_nonfilesystem (by rw [handoff.action]; intro impossible; cases impossible)) catalogue
  apply retained_joint prior joint registered catalogue family
  change CustodyOwnershipStep next.source.custody.catalogue tick prior.custody.current.source.custody.caps.family
    next.source.custody.caps.family
  rw [catalogue, family]
  have entries := launch_entries (handoff.action ▸ tick.operation)
  exact nonremoving_ownership_step _ (by intro parent name object bound; rwa [entries])
    (by intro object allocated; rfl)

-- §FS-host-boundary.ownership: This actual row retains its exact joint ownership/label history.
theorem engine_retirement_registered_publication_joint {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    (sdk : RuntimeDescriptorContract runtime) (descriptors : DescriptorContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (objects : ObjectLifetimeContract runtime) (metadata : LiveMetadataContract runtime child)
    (authority : GlobalAuthorityContract runtime child)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {all processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {callers : NativeProcesses}
    {actor : ActorId} {observation : EngineRetirement} (action : tick.action = .retire actor observation)
    (prior : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before callers) (joint : JointPublicationPrefix prior) :
    ∃ next : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after callers, JointPublicationPrefix next := by
  have kind : actionFamily tick.action = .retirement := by rw [action]; rfl
  obtain ⟨next, catalogue, family⟩ := retirement_custody_state_retained sdk descriptors lifetimes references objects metadata
    authority lookup kind prior.custody.current
  let registered := prior.custody.other next
    (no_root_use_of_nonfilesystem (by rw [kind]; intro impossible; cases impossible)) catalogue
  apply retained_joint prior joint registered catalogue family
  change CustodyOwnershipStep next.source.custody.catalogue tick prior.custody.current.source.custody.caps.family
    next.source.custody.caps.family
  rw [catalogue, family]
  have entries := retirement_entries sdk.toRetirementContract tick.operation kind
  exact nonremoving_ownership_step _ (by intro parent name object bound; rwa [entries])
    (by intro object allocated; rfl)

-- §FS-host-boundary.ownership: This actual row retains its exact joint ownership/label history.
theorem native_retirement_registered_publication_joint {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    (sdk : RuntimeDescriptorContract runtime) (descriptors : DescriptorContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (objects : ObjectLifetimeContract runtime) (metadata : LiveMetadataContract runtime child)
    (authority : GlobalAuthorityContract runtime child)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {all processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {before after : NativeProcesses}
    (exit : NativeRetirementAt tick before after)
    (prior : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before before) (joint : JointPublicationPrefix prior) :
    ∃ next : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after after, JointPublicationPrefix next := by
  have kind : actionFamily tick.action = .retirement := by rw [exit.action]; rfl
  obtain ⟨base, catalogue, family⟩ := retirement_custody_state_retained sdk descriptors lifetimes references objects metadata
    authority lookup kind prior.custody.current
  let next : CustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after after := {
    source := base.source
    nativePublic := fun object held => base.nativePublic object (native_retirement_held_before sdk.toRetirementContract exit held)
    nativeLive := fun object held => base.nativeLive object (native_retirement_held_before sdk.toRetirementContract exit held)
    directoriesPublic := base.directoriesPublic
    directoriesLive := base.directoriesLive
    births := base.births }
  let registered := prior.custody.other next
    (no_root_use_of_nonfilesystem (by rw [kind]; intro impossible; cases impossible)) catalogue
  apply retained_joint prior joint registered catalogue family
  change CustodyOwnershipStep base.source.custody.catalogue tick prior.custody.current.source.custody.caps.family
    base.source.custody.caps.family
  rw [catalogue, family]
  have entries := retirement_entries sdk.toRetirementContract tick.operation kind
  exact nonremoving_ownership_step _ (by intro parent name object bound; rwa [entries])
    (by intro object allocated; rfl)

end LeanCage.Host.Kernel
