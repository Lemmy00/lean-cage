import FilesystemRunFileRoot
import FilesystemJointDescendants

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: Actual validator/archive exclusive creation
-- derives the SAME run birth, private parent and current comparison from
-- source, then extends joint custody on success, error or lost reply.
theorem actual_run_file_publication_joint {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {semantics : NameSemanticsView} {dataObjects directories : ObjectId → Prop}
    (namespaceLaws : ByteNamespaceContract kernel semantics dataObjects)
    (descriptors : DescriptorContract kernel) (aliases : DirectoryAliasContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime) (raw : RawReferenceLifetimeContract kernel)
    (environment : InterferenceContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (accounts : AccountContract kernel hostUid) (objects : ObjectLifetimeContract runtime)
    (metadata : LiveMetadataContract runtime child) (authority : GlobalAuthorityContract runtime child)
    (nativeMetadata : NativeMetadataContract native) (lookup : LookupMutationContract (runtime := runtime) child native)
    (types : CreationTypeContract kernel directories) (probes : LookupPrimitiveContract kernel.step kernel.interference semantics)
    {initial : World} {final : Population} {all processed : List (ActorTick runtime)}
    (targets : OpenTargetContract kernel semantics initial.allocated dataObjects)
    (mounts : MountContract kernel initial.allocated)
    (dataLookup : DynamicDataLookupContract kernel semantics initial.allocated dataObjects)
    (cwdLookup : WorkingDirectoryContract kernel initial.allocated dataObjects)
    (journal : ActorJournal runtime (Population.empty initial) all final)
    (anchor : TemporaryAnchor initial) (anchorLookup : TemporaryLookupContract kernel anchor)
    (anchors : SystemAnchorJournal runtime anchor semantics (Population.empty initial) all final)
    (authorityProfile : NativeAuthorityProfile native all hostUid) (lookupProfile : NativeLookupProfile native all hostUid)
    {before after : Processes} {first last : NativeProcesses}
    (recording : NativeExternalJournal process child native hostUid before first all after last)
    {backend : NativeAuthorityJournal recording}
    {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    {foreignReferences : ForeignReferences} {currentNative : NativeProcesses}
    (prior : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative)
    (joint : JointPublicationPrefix prior)
    {trailing : List (ActorTick runtime)} (whole : all = processed ++ tick :: trailing)
    (call : RunFileCall adapter.occurrence.logicalBefore request) (exclusive : ExclusiveFile request) :
    ∃ next : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
        foreignReferences (processed ++ [tick]) tick.after currentNative, JointPublicationPrefix next := by
  have selected : all[processed.length]? = some tick := by
    rw [whole, List.getElem?_append_right (by omega)]
    simp only [Nat.sub_self, List.getElem?_cons_zero]
  have primary : request = adapter.occurrence.primary := guarded_namespace_origin (event := (request, observed))
    adapter.occurrence.adapter (by simp) (.inl exclusive.1)
  obtain ⟨resources⟩ := actual_run_file_resources descriptors lifetimes references environment journal selected present adapter call primary
  obtain ⟨root⟩ := actual_run_file_root descriptors lifetimes mounts journal prior.custody whole present resources exclusive.1
  obtain ⟨original, sameHandle, beforeGuard⟩ := resources.observed
  obtain ⟨identity⟩ := resources.source.uid_sample
  have uid := sampled_uid_is_host accounts identity
  let observation : ObservedDirectory kernel (fun ordinal query reply =>
      SourceReturnAt runtime all actor ordinal Reply (.filesystem query) reply)
      engine.events.length (tick.before.project engine) hostUid call.directory.directory := {
    handle := original.handle
    live := original.live
    raw := original.raw
    sample := original.sample
    earlier := original.earlier
    trusted := uid ▸ original.trusted }
  have live : engine.references call.directory.directory.fd = some observation.handle := observation.live
  obtain ⟨interval, intervalHandle, intervalOrdinal⟩ := checked_parent_interval_owned (backend := backend) descriptors lifetimes
    references raw sdk accounts journal recording selected present observation live observation.earlier
  obtain ⟨parentArgument, mode, component⟩ := call.kind.arguments call.directory.directory.fd call.active exclusive
  have operandLive : engine.references request.first = some observation.handle := by rw [parentArgument]; exact live
  have different : request.first ≠ cwd := by
    rw [parentArgument]
    exact SourceReadForms.descriptor_not_cwd (SourceReadForms.descriptor_fits resources.source.opening.recognized)
  have member : request.first ∈ Lookup.parents request := by simp [Lookup.parents, exclusive.1, different]
  obtain ⟨information, known, trusted, names⟩ := checked_parent_comparison lifetimes authority nativeMetadata lookup probes
    journal authorityProfile lookupProfile interval adapter (.inl exclusive.1) request.first member
    observation.handle operandLive (by rw [intervalHandle]) (by rw [intervalOrdinal]; exact beforeGuard)
  have comparison : (semantics.at tick.before.shared observation.handle.object).byteExact := by
    simpa only [intervalHandle] using names
  have privateParent : prior.custody.current.source.custody.caps.family observation.handle.object = some root.root.object := by
    change prior.custody.current.source.custody.caps.family original.handle.object = some root.root.object
    rw [sameHandle, root.directory]
    exact root.privateRoot
  exact descendant_registered_publication_joint namespaceLaws descriptors aliases lifetimes references sdk accounts objects
    metadata types lookup targets dataLookup cwdLookup journal anchor anchorLookup anchors selected whole rfl action present
    (.inr exclusive) (fun making => by rw [exclusive.1] at making; cases making) component operandLive comparison prior joint privateParent

end LeanCage.Host.Kernel
