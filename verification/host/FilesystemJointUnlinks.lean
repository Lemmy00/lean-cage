import FilesystemPublicationCleanupJoint
import FilesystemRunCleanup

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: The actual entrypoint classifies every raw
-- unlink, so callers provide no cleanup role, private parent or source
-- footprint. Run, validator and publication failures share the same fold.
theorem actual_source_unlink_publication_joint {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {semantics : NameSemanticsView} {dataObjects directories : ObjectId → Prop}
    (namespaceLaws : ByteNamespaceContract kernel semantics dataObjects)
    (frames : ByteNamespaceFrameContract kernel semantics) (otherDirectories : UnlinkDirectoryFrameContract kernel)
    (descriptors : DescriptorContract kernel) (aliases : DirectoryAliasContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime) (raw : RawReferenceLifetimeContract kernel)
    (environment : InterferenceContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (accounts : AccountContract kernel hostUid) (objects : ObjectLifetimeContract runtime)
    (metadata : LiveMetadataContract runtime child) (authority : GlobalAuthorityContract runtime child)
    (nativeMetadata : NativeMetadataContract native) (lookup : LookupMutationContract (runtime := runtime) child native)
    (probes : LookupPrimitiveContract kernel.step kernel.interference semantics)
    {initial : World} {final : Population} {all processed : List (ActorTick runtime)}
    (targets : OpenTargetContract kernel semantics initial.allocated dataObjects)
    (mounts : MountContract kernel initial.allocated)
    (journal : ActorJournal runtime (Population.empty initial) all final)
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
    (unlink : request.op = .unlinkAt) :
    ∃ next : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
        foreignReferences (processed ++ [tick]) tick.after currentNative,
      next.custody.current.source.custody.catalogue = prior.custody.current.source.custody.catalogue ∧
      next.custody.current.source.custody.caps.family = prior.custody.current.source.custody.caps.family ∧
      JointPublicationPrefix next := by
  have primary : request = adapter.occurrence.primary := primitive_mutation_primary adapter.occurrence (by
    intro passive
    simp only [NamespacePassive, unlink] at passive)
  have logical := PrimitiveFilesystem.filesystem_occurrence_logical adapter.occurrence
  rw [← primary] at logical
  have logical : Program.Prefix Entrypoint.run
      (adapter.occurrence.logicalBefore ++ [Program.filesystemPrefixEvent (request, none)]) := logical
  obtain ⟨site⟩ := entrypoint_unlink_site logical unlink
  cases site with
  | cleanup source =>
    exact actual_run_cleanup_origin_joint (backend := backend) namespaceLaws frames otherDirectories descriptors lifetimes
      references environment raw sdk accounts objects metadata authority nativeMetadata lookup probes mounts journal
      authorityProfile lookupProfile recording action present adapter prior joint whole source unlink rfl [] (by simp)
  | publication invocation =>
    obtain ⟨call⟩ := PublicationCleanup.host_unlink_source invocation unlink
    exact actual_publication_cleanup_unlink_joint (backend := backend) namespaceLaws frames otherDirectories descriptors aliases
      lifetimes references raw environment sdk accounts objects metadata authority nativeMetadata lookup probes targets mounts journal
      authorityProfile lookupProfile recording action present adapter prior joint whole call unlink

end LeanCage.Host.Kernel
