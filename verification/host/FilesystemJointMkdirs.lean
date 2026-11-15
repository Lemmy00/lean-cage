import FilesystemPreparingMkdirJoint
import FilesystemStagingAuthority
import FilesystemTraversalAuthority

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: Every actual caller mkdir selects its real
-- run, public ancestor, fresh stage or interrupted-fill source internally.
-- No private parent, helper footprint, root binding or later ACK is supplied.
theorem actual_source_mkdir_publication_joint {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
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
    (mkdir : request.op = .mkdirAt) :
    ∃ next : RegisteredPublicationState runtime initial all hostUid dataObjects directories semantics
        foreignReferences (processed ++ [tick]) tick.after currentNative, JointPublicationPrefix next := by
  have selected : all[processed.length]? = some tick := by
    rw [whole, List.getElem?_append_right (by omega)]
    simp only [Nat.sub_self, List.getElem?_cons_zero]
  have primary : request = adapter.occurrence.primary := primitive_mutation_primary adapter.occurrence (by
    intro passive
    simp only [NamespacePassive, mkdir] at passive)
  have logical := PrimitiveFilesystem.filesystem_occurrence_logical adapter.occurrence
  rw [← primary] at logical
  have logical : Program.Prefix Entrypoint.run
      (adapter.occurrence.logicalBefore ++ [Program.filesystemPrefixEvent (request, none)]) := logical
  obtain ⟨site⟩ := entrypoint_mkdir_site logical mkdir
  cases site with
  | creating invocation =>
    obtain ⟨source⟩ := primitive_run_parent_observations adapter invocation mkdir
    exact run_creation_registered_publication_joint (backend := backend) namespaceLaws descriptors lifetimes references raw sdk
      accounts objects metadata types authority nativeMetadata lookup probes journal anchor anchorLookup anchors authorityProfile
      lookupProfile recording selected action present source prior joint
  | publishing invocation =>
    obtain ⟨source⟩ := PublicationCreation.host_mkdir_site invocation mkdir
    cases classified : source.source.site with
    | selecting context inside cursor trace =>
      let call : TraversalCall adapter.occurrence.logicalBefore request := ⟨source, context, inside, cursor, trace, classified⟩
      obtain ⟨parent⟩ := actual_primitive_traversal_authority (backend := backend) descriptors lifetimes references raw sdk accounts
        authority nativeMetadata lookup probes journal authorityProfile lookupProfile recording selected present adapter call mkdir
      exact public_creation_registered_publication_joint namespaceLaws descriptors aliases accounts lifetimes references objects
        metadata lookup journal dataLookup cwdLookup selected action present parent whole rfl prior joint sdk
    | staging context inside child trace =>
      let call : StagingCall adapter.occurrence.logicalBefore request := ⟨source, context, inside, child, trace, classified⟩
      obtain ⟨parent⟩ := actual_primitive_staging_authority (backend := backend) descriptors aliases lifetimes references raw sdk
        accounts authority nativeMetadata lookup probes journal authorityProfile lookupProfile recording selected present adapter call mkdir
      exact staging_creation_registered_publication_joint namespaceLaws descriptors aliases accounts lifetimes references objects
        metadata types lookup journal dataLookup cwdLookup selected action present parent mkdir whole prior joint sdk
    | filling context inside active trace =>
      let call := PublicationPreparing.Call.of_creation_fill source context inside active trace
      exact actual_preparing_mkdir_joint (backend := backend) namespaceLaws descriptors aliases lifetimes references raw environment
        sdk accounts objects metadata authority nativeMetadata lookup types probes targets mounts dataLookup cwdLookup journal anchor
        anchorLookup anchors authorityProfile lookupProfile recording action present adapter prior joint whole call mkdir

end LeanCage.Host.Kernel
