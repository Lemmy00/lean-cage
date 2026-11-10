import FilesystemRegisteredCustody

namespace LeanCage.Host.Kernel

-- §FS-host-boundary.ownership: One actual native operation retains all registered source
-- histories. Its callback operands/profile are per-row, not a complete callback frame.
theorem native_registered_custody {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {primitive : NativePrimitive kernel} {hostUid : Nat} {semantics : NameSemanticsView}
    {dataObjects directories : ObjectId → Prop}
    (namespaceLaws : NativeNamespaceContract primitive) (metadata : NativeLiveMetadataContract primitive)
    (heldMetadata : NativeMetadataContract primitive) (descriptors : DescriptorContract kernel)
    (sdk : RuntimeDescriptorContract runtime) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (objects : ObjectLifetimeContract runtime)
    (lookup : NativeNonemptyLookupContract primitive semantics)
    {initial : World} {final : Population} {all processed : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    (boundaryProfile : NativeBoundaryAuthorityProfile primitive all hostUid)
    {position : Nat} {tick : ActorTick runtime} (selected : all[position]? = some tick)
    {before after : NativeProcesses} (call : NativeCallAt primitive tick before after)
    {foreignReferences : ForeignReferences}
    (prior : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before before)
    (profile : NativePrivateOperandProfile namespaceLaws call prior.current.source.custody.caps.family) :
    Nonempty (RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after after) := by
  obtain ⟨next, nativePublic, nativeLive, caps, catalogue⟩ := native_custody_prefix_current namespaceLaws metadata
    heldMetadata descriptors lifetimes references objects lookup journal boundaryProfile selected call prior.current.source
    profile prior.current.nativePublic
  have notLaunch : ∀ actor references closeExec directory, tick.action ≠ .launch actor references closeExec directory := by
    intro actor references closeExec directory impossible
    rw [call.action] at impossible
    cases impossible
  have labels : ExistingLabels tick.before.shared tick.after.shared
      prior.current.source.custody.caps.family next.custody.caps.family := by
    rw [caps]
    exact unchanged_existing_labels _ _ _
  obtain ⟨liveDirectories, publicDirectories⟩ := nonlaunch_directories_custody sdk lifetimes tick.operation notLaunch
    prior.current.directoriesLive prior.current.directoriesPublic labels
  have ownership : CustodyOwnershipStep next.custody.catalogue tick
      prior.current.source.custody.caps.family next.custody.caps.family := by
    rw [caps, catalogue]
    exact native_namespace_ownership_step namespaceLaws prior.current.source.custody.catalogue call profile
  have included : ∀ record ∈ prior.current.source.custody.catalogue, record ∈ next.custody.catalogue := by
    rw [catalogue]
    exact fun _ member => member
  have old : ∀ record ∈ next.custody.catalogue, record ∈ prior.current.source.custody.catalogue := by
    rw [catalogue]
    exact fun _ member => member
  let state : CustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after after :=
    ⟨next, nativePublic, nativeLive, publicDirectories, liveDirectories,
      catalogue_birth_scopes_existing included old prior.current.births ownership labels
        (fun object => actor_step_allocated lifetimes tick.operation object)⟩
  refine ⟨prior.other state ?_ catalogue⟩
  exact no_root_use_of_nonfilesystem (by rw [call.action]; intro impossible; cases impossible)

end LeanCage.Host.Kernel
