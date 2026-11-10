import FilesystemForeignCustody
import FilesystemRuntimeCustody
import FilesystemRegisteredLifecycle
import FilesystemPublicationProgress

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: These are the actual nonpublication cases of the
-- cumulative journal. Every step retains the exact family/catalogue fields;
-- real resource retirement and external namespace changes remain in its input row.
theorem runtime_registered_publication {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
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
      foreignReferences processed tick.before callers) :
    Nonempty (RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after callers) := by
  obtain ⟨next, catalogue, family⟩ := runtime_registered_custody_retained namespaces sdk descriptors lifetimes references
    objects metadata heldMetadata lookup kind prior.custody
  exact ⟨prior.preserved next catalogue (by intro object allocated; exact congrFun family object)⟩

theorem ordinary_registered_publication {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
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
      foreignBefore processed tick.before callers) :
    Nonempty (RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignAfter (processed ++ [tick]) tick.after callers) := by
  obtain ⟨next, catalogue, family⟩ := ordinary_registered_custody_retained foreign authority descriptors lifetimes references
    sdk objects metadata lookup recorded action allowed view directoryParents observed prior.custody
  exact ⟨prior.preserved next catalogue (by intro object allocated; exact congrFun family object)⟩

theorem native_registered_publication {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
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
    (profile : NativePrivateOperandProfile namespaceLaws call prior.custody.current.source.custody.caps.family) :
    Nonempty (RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after after) := by
  obtain ⟨next, catalogue, family⟩ := native_custody_state_retained namespaceLaws metadata heldMetadata descriptors sdk
    lifetimes references objects lookup journal boundaryProfile selected call prior.custody.current profile
  let registered := prior.custody.other next
    (no_root_use_of_nonfilesystem (by rw [call.action]; intro impossible; cases impossible)) catalogue
  exact ⟨prior.preserved registered catalogue (by intro object allocated; exact congrFun family object)⟩

theorem handoff_registered_publication {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
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
      foreignReferences processed tick.before before) :
    Nonempty (RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after (before.transfer handoff.actor handoff.execution)) := by
  obtain ⟨next, catalogue, family⟩ := handoff_custody_state_retained descriptors lifetimes references handoff binding separate
    prior.custody.current
  let registered := prior.custody.other next
    (no_root_use_of_nonfilesystem (by rw [handoff.action]; intro impossible; cases impossible)) catalogue
  exact ⟨prior.preserved registered catalogue (by intro object allocated; exact congrFun family object)⟩

theorem engine_retirement_registered_publication {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
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
      foreignReferences processed tick.before callers) :
    Nonempty (RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after callers) := by
  have kind : actionFamily tick.action = .retirement := by rw [action]; rfl
  obtain ⟨next, catalogue, family⟩ := retirement_custody_state_retained sdk descriptors lifetimes references objects metadata
    authority lookup kind prior.custody.current
  let registered := prior.custody.other next
    (no_root_use_of_nonfilesystem (by rw [kind]; intro impossible; cases impossible)) catalogue
  exact ⟨prior.preserved registered catalogue (by intro object allocated; exact congrFun family object)⟩

theorem native_retirement_registered_publication {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
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
      foreignReferences processed tick.before before) :
    Nonempty (RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after after) := by
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
  exact ⟨prior.preserved registered catalogue (by intro object allocated; exact congrFun family object)⟩

end LeanCage.Host.Kernel
