import FilesystemPreparingExclusiveJoint
import FilesystemPublicationExclusiveSource
import FilesystemRunFileJoint
import FilesystemExclusiveSites

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: Every actual exclusive file open selects
-- its real validator, archive or interrupted publisher source internally.
-- No private parent, helper footprint, root binding or later ACK is supplied.
theorem actual_source_exclusive_publication_joint {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
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
    (exclusive : ExclusiveFile request) :
    ∃ next : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
        foreignReferences (processed ++ [tick]) tick.after currentNative, JointPublicationPrefix next := by
  have primary : request = adapter.occurrence.primary := primitive_mutation_primary adapter.occurrence
    (fun passive => passive_not_exclusive passive exclusive)
  have logical := PrimitiveFilesystem.filesystem_occurrence_logical adapter.occurrence
  rw [← primary] at logical
  have logical : Program.Prefix Entrypoint.run
      (adapter.occurrence.logicalBefore ++ [Program.filesystemPrefixEvent (request, none)]) := logical
  obtain ⟨site⟩ := entrypoint_exclusive_site logical exclusive
  cases site with
  | file call =>
    exact actual_run_file_publication_joint (backend := backend) namespaceLaws descriptors aliases lifetimes references raw
      environment sdk accounts objects metadata authority nativeMetadata lookup types probes targets mounts dataLookup cwdLookup
      journal anchor anchorLookup anchors authorityProfile lookupProfile recording action present adapter prior joint whole call exclusive
  | publication invocation =>
    obtain ⟨call⟩ := PublicationExclusive.preparing_of_exclusive invocation exclusive
    exact actual_preparing_exclusive_joint (backend := backend) namespaceLaws descriptors aliases lifetimes references raw
      environment sdk accounts objects metadata authority nativeMetadata lookup types probes targets mounts dataLookup cwdLookup
      journal anchor anchorLookup anchors authorityProfile lookupProfile recording action present adapter prior joint whole call exclusive

end LeanCage.Host.Kernel
