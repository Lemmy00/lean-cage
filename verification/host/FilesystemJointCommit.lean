import FilesystemCommitPublication
import FilesystemOwnershipRetention

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.publication: The actual commit extends the SAME joint
-- prefix using its real unchanged-or-committed delta. A returned error or
-- missing acknowledgement never supplies a rollback or success inference.
theorem actual_commit_publication_joint {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {semantics : NameSemanticsView} {dataObjects directories : ObjectId → Prop}
    (namespaceLaws : ByteNamespaceContract kernel semantics dataObjects) (namespaceFrames : ByteNamespaceFrameContract kernel semantics)
    (descriptors : DescriptorContract kernel) (aliases : DirectoryAliasContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (environment : InterferenceContract kernel) (raw : RawReferenceLifetimeContract kernel)
    (sdk : RuntimeDescriptorContract runtime) (accounts : AccountContract kernel hostUid)
    (objects : ObjectLifetimeContract runtime) (liveMetadata : LiveMetadataContract runtime child)
    (metadata : GlobalAuthorityContract runtime child) (nativeMetadata : NativeMetadataContract native)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    (probes : LookupPrimitiveContract kernel.step kernel.interference semantics)
    {initial : World} {final : Population} {all processed : List (ActorTick runtime)}
    (mounts : MountContract kernel initial.allocated)
    (journal : ActorJournal runtime (Population.empty initial) all final)
    (authorityProfile : NativeAuthorityProfile native all hostUid) (lookupProfile : NativeLookupProfile native all hostUid)
    {priorProcesses afterProcesses : Processes} {firstNative lastNative : NativeProcesses}
    (recording : NativeExternalJournal process child native hostUid priorProcesses firstNative all afterProcesses lastNative)
    {backend : NativeAuthorityJournal recording}
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {currentNative : NativeProcesses}
    (prior : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative)
    (joint : JointPublicationPrefix prior)
    {trailing : List (ActorTick runtime)} (whole : all = processed ++ tick :: trailing)
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    (moving : request.op = .renameNew) :
    ∃ commit : PublicationCommitStep runtime prior actor engine request observed,
      JointPublicationPrefix commit.updated := by
  obtain ⟨commit⟩ := actual_commit_registered_publication (backend := backend) namespaceLaws namespaceFrames descriptors
    aliases lifetimes references environment raw sdk accounts objects liveMetadata metadata nativeMetadata lookup probes
    mounts journal authorityProfile lookupProfile recording prior whole action present adapter moving
  have actual := selected_filesystem_step tick action present
  have ownership : CustodyOwnershipStep commit.updated.custody.current.source.custody.catalogue tick
      prior.custody.current.source.custody.caps.family commit.updated.custody.current.source.custody.caps.family := by
    rw [commit.sameCatalogue]
    rcases commit.effect with unchanged | committed
    · have family := congrArg Capabilities.family unchanged.2
      rw [family]
      exact nonremoving_ownership_step _ (by intro parent name object bound; rwa [unchanged.1])
        (by intro object allocated; rfl)
    · have family := congrArg Capabilities.family committed.2
      rw [family]
      exact source_publication_ownership_step_byte namespaceFrames commit.root actual action moving
        commit.authority.byte_operands
  have labels : ExistingLabels tick.before.shared tick.after.shared prior.custody.current.source.custody.caps.family
      commit.updated.custody.current.source.custody.caps.family := by
    rcases commit.effect with unchanged | committed
    · rw [congrArg Capabilities.family unchanged.2]
      exact unchanged_existing_labels _ _ _
    · rw [congrArg Capabilities.family committed.2]
      exact (FamilyUpdate.published commit.root.root.object).existing
  refine ⟨commit, joint.advance commit.updated ?_ ⟨ownership, labels⟩⟩
  rw [commit.sameCatalogue]
  exact fun _ member => member

end LeanCage.Host.Kernel
