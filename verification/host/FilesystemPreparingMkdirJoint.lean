import FilesystemPreparingMkdir
import FilesystemJointDescendants

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: The selected actual interrupted-fill
-- mkdir derives its original root, retained checked parent and comparison,
-- then advances the SAME joint custody/publication history on every reply.
theorem actual_preparing_mkdir_joint {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
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
    (call : PublicationPreparing.Call adapter.occurrence.logicalBefore request) (mkdir : request.op = .mkdirAt) :
    ∃ next : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
        foreignReferences (processed ++ [tick]) tick.after currentNative, JointPublicationPrefix next := by
  have selected : all[processed.length]? = some tick := by
    rw [whole, List.getElem?_append_right (by omega)]
    simp only [Nat.sub_self, List.getElem?_cons_zero]
  have primary : request = adapter.occurrence.primary := guarded_namespace_origin (event := (request, observed))
    adapter.occurrence.adapter (by simp) (.inr (.inl mkdir))
  obtain ⟨resources⟩ := actual_preparing_stage_resources descriptors aliases lifetimes references environment journal selected
    present adapter call primary
  obtain ⟨root⟩ := actual_preparing_root_from_resources descriptors lifetimes mounts journal prior.custody whole present adapter
    resources primary
  have currentOpens := actual_private_directory_opens descriptors lifetimes targets journal selected present whole rfl
    prior.custody.current.source.custody.history
  have opens : PrivateDirectoryOpens kernel (fun ordinal query reply before after =>
      SourceReturnAt runtime all resources.source.earlier.source.inputActor ordinal Reply (.filesystem query) reply before after ∧
        ordinal < engine.events.length) prior.custody.current.source.custody.caps.family := by
    simpa only [resources.sameActor] using currentOpens
  have privateRoot : prior.custody.current.source.custody.caps.family resources.source.earlier.source.opening.handle.object =
      some root.root.object := by rw [root.directory]; exact root.privateRoot
  obtain ⟨parent⟩ := resources.mkdir_parent descriptors primary mkdir opens privateRoot
  obtain ⟨identity⟩ := preparing_stage_uid_sample descriptors adapter call
  have uid := sampled_uid_is_host accounts identity
  let original := parent.current.observation
  let observation : ObservedDirectory kernel (fun ordinal query reply =>
      SourceReturnAt runtime all actor ordinal Reply (.filesystem query) reply)
      engine.events.length (tick.before.project engine) hostUid parent.current.directory := {
    handle := original.handle
    live := original.live
    raw := original.raw
    sample := original.sample
    earlier := original.earlier
    trusted := uid ▸ original.trusted }
  have live : engine.references parent.current.directory.fd = some observation.handle := observation.live
  obtain ⟨interval, sameHandle, sameOrdinal⟩ := checked_parent_interval_owned (backend := backend) descriptors lifetimes
    references raw sdk accounts journal recording selected present observation live observation.earlier
  have operandLive : engine.references request.first = some observation.handle := parent.current.operand ▸ live
  have member : request.first ∈ Lookup.parents request := by simp only [Lookup.parents, mkdir, List.mem_singleton]
  obtain ⟨information, known, trusted, names⟩ := checked_parent_comparison lifetimes authority nativeMetadata lookup probes
    journal authorityProfile lookupProfile interval adapter (.inr (.inl mkdir)) request.first member
    observation.handle operandLive (by rw [sameHandle]) (by rw [sameOrdinal]; exact parent.beforeGuard)
  have comparison : (semantics.at tick.before.shared observation.handle.object).byteExact := by
    simpa only [sameHandle] using names
  exact descendant_registered_publication_joint namespaceLaws descriptors aliases lifetimes references sdk accounts objects
    metadata types lookup targets dataLookup cwdLookup journal anchor anchorLookup anchors selected whole rfl action present
    (.inl mkdir) parent.current.mode parent.current.component operandLive comparison prior joint parent.current.privateParent

end LeanCage.Host.Kernel
