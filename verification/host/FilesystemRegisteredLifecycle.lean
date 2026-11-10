import FilesystemRegisteredCustody
import FilesystemRetirementCustody

namespace LeanCage.Host.Kernel

-- §FS-host-boundary.caller: The actual exec handoff transfers its raw/SDK tables
-- and CWD on this same row, while retaining every prior creation registration.
theorem handoff_registered_custody {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime)
    {initial : World} {all processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories ipc : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {before : NativeProcesses}
    (handoff : NativeHandoffAt tick before)
    (binding : InitialEngineBinding ipc handoff.execution.references.rawProjection.handles
      handoff.execution.references.rawProjection.closeOnExec)
    (separate : ∀ object, ipc object → ¬ dataObjects object)
    (prior : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before before) :
    Nonempty (RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after (before.transfer handoff.actor handoff.execution)) := by
  obtain ⟨next, catalogue⟩ := handoff_custody_state_catalogued descriptors lifetimes references handoff binding separate prior.current
  refine ⟨prior.other next ?_ catalogue⟩
  exact no_root_use_of_nonfilesystem (by rw [handoff.action]; intro impossible; cases impossible)

-- §FS-host-boundary.ownership: An actual exit observation retires only its
-- observed resources. Old catalogue/birth ownership survives orphaned directories.
theorem engine_retirement_registered_custody {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
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
    (prior : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before callers) :
    Nonempty (RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after callers) := by
  have kind : actionFamily tick.action = .retirement := by rw [action]; rfl
  obtain ⟨next, catalogue⟩ := retirement_custody_state_catalogued sdk descriptors lifetimes references objects metadata
    authority lookup kind prior.current
  exact ⟨prior.other next (no_root_use_of_nonfilesystem (by rw [kind]; intro impossible; cases impossible)) catalogue⟩

theorem native_retirement_registered_custody {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
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
    (prior : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before before) :
    Nonempty (RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after after) := by
  have kind : actionFamily tick.action = .retirement := by rw [exit.action]; rfl
  obtain ⟨base, catalogue⟩ := retirement_custody_state_catalogued sdk descriptors lifetimes references objects metadata
    authority lookup kind prior.current
  let next : CustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after after := {
    source := base.source
    nativePublic := fun object held => base.nativePublic object
      (native_retirement_held_before sdk.toRetirementContract exit held)
    nativeLive := fun object held => base.nativeLive object
      (native_retirement_held_before sdk.toRetirementContract exit held)
    directoriesPublic := base.directoriesPublic
    directoriesLive := base.directoriesLive
    births := base.births }
  exact ⟨prior.other next (no_root_use_of_nonfilesystem (by rw [kind]; intro impossible; cases impossible)) catalogue⟩

end LeanCage.Host.Kernel
