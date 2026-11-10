import FilesystemCustodyPrefix
import FilesystemStagingAuthority
import FilesystemTraversalAuthority

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: The real run/validator mkdir extends the SAME custody prefix,
-- including catalogue ownership of every retained peer FD and committed-error/lost births.
theorem run_creation_prefix {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat} {semantics : NameSemanticsView}
    {dataObjects directories : ObjectId → Prop}
    (namespaceLaws : ByteNamespaceContract kernel semantics dataObjects)
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (raw : RawReferenceLifetimeContract kernel)
    (sdk : RuntimeDescriptorContract runtime) (accounts : AccountContract kernel hostUid)
    (objects : ObjectLifetimeContract runtime) (liveMetadata : LiveMetadataContract runtime child)
    (types : CreationTypeContract kernel directories)
    (metadata : GlobalAuthorityContract runtime child) (nativeMetadata : NativeMetadataContract native)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    (probes : LookupPrimitiveContract kernel.step kernel.interference semantics)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    (anchor : TemporaryAnchor initial) (anchorLookup : TemporaryLookupContract kernel anchor)
    (anchors : SystemAnchorJournal runtime anchor semantics (Population.empty initial) ticks final)
    (authorityProfile : NativeAuthorityProfile native ticks hostUid) (lookupProfile : NativeLookupProfile native ticks hostUid)
    {first last : Processes} {callers next : NativeProcesses}
    (recording : NativeExternalJournal process child native hostUid first callers ticks last next)
    {backend : NativeAuthorityJournal recording}
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState} {request : Request}
    {observed : Option Reply} (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (source : PrimitiveRunParent runtime initial ticks tick actor engine request)
    {processed : List (ActorTick runtime)} {foreignReferences : ForeignReferences}
    (prior : CustodyPrefix runtime initial ticks hostUid dataObjects directories semantics foreignReferences processed tick.before) :
    Nonempty (CustodyPrefix runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after) := by
  obtain ⟨afterCaps, afterCatalogue, state, coverage, valid, names, labels, update, included, origin⟩ :=
    actual_primitive_run_creation_with_flow (backend := backend) namespaceLaws descriptors lifetimes references raw sdk accounts
      objects liveMetadata types metadata nativeMetadata lookup probes journal anchor anchorLookup anchors
      authorityProfile lookupProfile recording selected action present source prior.namespaceState prior.names
      prior.catalogue prior.coverage prior.valid
  exact ⟨prior.advance_retained descriptors lifetimes references afterCaps afterCatalogue state names coverage valid
    update included action (by simp only [source.mkdir, RetainsDescriptors]; decide)⟩

-- §FS-host-boundary.ownership: Staging extends that same source/native history and derives its
-- public parent from the caller's actual path; no supplied public-FD or private-root role occurs.
theorem staging_creation_prefix {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat} {semantics : NameSemanticsView}
    {dataObjects directories : ObjectId → Prop}
    (namespaceLaws : ByteNamespaceContract kernel semantics dataObjects)
    (descriptors : DescriptorContract kernel) (aliases : DirectoryAliasContract kernel)
    (accounts : AccountContract kernel hostUid) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (objects : ObjectLifetimeContract runtime)
    (liveMetadata : LiveMetadataContract runtime child) (types : CreationTypeContract kernel directories)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    (dataLookup : DynamicDataLookupContract kernel semantics initial.allocated dataObjects)
    (cwdLookup : WorkingDirectoryContract kernel initial.allocated dataObjects)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState} {request : Request}
    {observed : Option Reply} (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (authority : PrimitiveStagingAuthority runtime initial ticks tick actor engine request observed hostUid semantics)
    (mkdir : request.op = .mkdirAt)
    {processed trailing : List (ActorTick runtime)} {foreignReferences : ForeignReferences}
    (shape : ticks = processed ++ tick :: trailing) (count : processed.length = position)
    (prior : CustodyPrefix runtime initial ticks hostUid dataObjects directories semantics foreignReferences processed tick.before) :
    Nonempty (CustodyPrefix runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after) := by
  obtain ⟨afterCaps, afterCatalogue, state, coverage, valid, names, labels, update, included, origin⟩ :=
    actual_primitive_staging_creation_from_source namespaceLaws descriptors aliases accounts lifetimes objects
      liveMetadata types lookup journal dataLookup cwdLookup selected action present authority mkdir
      prior.namespaceState prior.names shape count prior.history prior.catalogue prior.coverage prior.valid
  exact ⟨prior.advance_retained descriptors lifetimes references afterCaps afterCatalogue state names coverage valid
    update included action (by simp only [mkdir, RetainsDescriptors]; decide)⟩

-- §FS-host-boundary.ownership: A public traversal creation preserves the same private catalogue
-- and raw-handle ownership, rather than registering a directory just because it was created.
theorem public_creation_prefix {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat} {semantics : NameSemanticsView}
    {dataObjects directories : ObjectId → Prop}
    (namespaceLaws : ByteNamespaceContract kernel semantics dataObjects)
    (descriptors : DescriptorContract kernel) (aliases : DirectoryAliasContract kernel)
    (accounts : AccountContract kernel hostUid) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (objects : ObjectLifetimeContract runtime)
    (liveMetadata : LiveMetadataContract runtime child)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    (dataLookup : DynamicDataLookupContract kernel semantics initial.allocated dataObjects)
    (cwdLookup : WorkingDirectoryContract kernel initial.allocated dataObjects)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState} {request : Request}
    {observed : Option Reply} (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (authority : PrimitiveTraversalAuthority runtime initial ticks tick actor engine request observed hostUid semantics)
    {processed trailing : List (ActorTick runtime)} {foreignReferences : ForeignReferences}
    (shape : ticks = processed ++ tick :: trailing) (count : processed.length = position)
    (prior : CustodyPrefix runtime initial ticks hostUid dataObjects directories semantics foreignReferences processed tick.before) :
    Nonempty (CustodyPrefix runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after) := by
  obtain ⟨state, coverage, valid, names, update⟩ := actual_primitive_public_creation namespaceLaws descriptors aliases
    accounts lifetimes objects liveMetadata lookup journal dataLookup cwdLookup selected action present authority
      prior.namespaceState prior.names shape count prior.history prior.catalogue prior.coverage prior.valid
  exact ⟨prior.advance_retained descriptors lifetimes references (prior.caps.retain tick.after.shared) prior.catalogue
    state names coverage valid update (by intro record member; exact member) action
    (by simp only [authority.resources.source.arguments.1, RetainsDescriptors]; decide)⟩

end LeanCage.Host.Kernel
