import FilesystemCreationPrefix
import FilesystemOwnershipPrefix

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: The actual run/validator mkdir simultaneously extends source
-- custody and exact removal provenance; the next state is never a supplied helper-safe premise.
theorem run_creation_ownership_prefix_catalogued {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
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
    (backend : PrimitiveChildAuthorityProducer child ticks)
    (authorityProfile : NativeAuthorityProfile native ticks hostUid) (lookupProfile : NativeLookupProfile native ticks hostUid)
    {first last : Processes} {callers next : NativeProcesses}
    (recording : NativeExternalJournal process child native hostUid first callers ticks last next)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState} {request : Request}
    {observed : Option Reply} (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (source : PrimitiveRunParent runtime initial ticks tick actor engine request)
    {processed : List (ActorTick runtime)} {foreignReferences : ForeignReferences}
    (prior : OwnershipPrefix runtime initial ticks hostUid dataObjects directories semantics foreignReferences processed tick.before) :
    ∃ after : OwnershipPrefix runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after,
      CurrentRootCreation prior.custody.caps prior.custody.catalogue after.custody.caps after.custody.catalogue tick position ∧
      CustodyOwnershipStep after.custody.catalogue tick prior.custody.caps.family after.custody.caps.family := by
  obtain ⟨afterCaps, afterCatalogue, state, coverage, valid, names, labels, update, included, origin, receipt⟩ :=
    actual_primitive_run_creation_catalogued namespaceLaws descriptors lifetimes references raw sdk accounts
      objects liveMetadata types metadata nativeMetadata lookup probes journal anchor anchorLookup anchors backend
      authorityProfile lookupProfile recording selected action present source prior.custody.namespaceState prior.custody.names
      prior.custody.catalogue prior.custody.coverage prior.custody.valid
  have change := primitive_run_mkdir_delta namespaceLaws descriptors lifetimes references raw sdk accounts
    metadata nativeMetadata lookup probes journal backend authorityProfile lookupProfile recording selected action present source
  have ownership : CustodyOwnershipStep afterCatalogue tick prior.custody.caps.family afterCaps.family :=
    nonremoving_ownership_step afterCatalogue (creation_retains_bindings (before := tick.before.project engine) change (.inl source.mkdir))
      receipt.labels
  let next := prior.custody.advance_retained descriptors lifetimes references afterCaps afterCatalogue state names coverage valid
    update included action (by simp only [source.mkdir, RetainsDescriptors]; decide)
  exact ⟨prior.advance next included ownership, receipt, ownership⟩

-- §AR-host-boundary.interfaces: Keep the prior ownership consumer while the stronger
-- sibling retains its exact current catalogue choice and per-operation removal proof.
theorem run_creation_ownership_prefix {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
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
    (backend : PrimitiveChildAuthorityProducer child ticks)
    (authorityProfile : NativeAuthorityProfile native ticks hostUid) (lookupProfile : NativeLookupProfile native ticks hostUid)
    {first last : Processes} {callers next : NativeProcesses}
    (recording : NativeExternalJournal process child native hostUid first callers ticks last next)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState} {request : Request}
    {observed : Option Reply} (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (source : PrimitiveRunParent runtime initial ticks tick actor engine request)
    {processed : List (ActorTick runtime)} {foreignReferences : ForeignReferences}
    (prior : OwnershipPrefix runtime initial ticks hostUid dataObjects directories semantics foreignReferences processed tick.before) :
    Nonempty (OwnershipPrefix runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after) := by
  obtain ⟨next, choice, ownership⟩ := run_creation_ownership_prefix_catalogued namespaceLaws descriptors lifetimes references raw sdk accounts objects liveMetadata types
      metadata nativeMetadata lookup probes journal anchor anchorLookup anchors backend authorityProfile lookupProfile
      recording selected action present source prior
  exact ⟨next⟩

-- §FS-host-boundary.ownership: Publication staging uses its actual source-selected parent
-- and SAME current birth receipt. Old roots and all interleaved owners retain their identity.
theorem staging_creation_ownership_prefix_catalogued {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
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
    (prior : OwnershipPrefix runtime initial ticks hostUid dataObjects directories semantics foreignReferences processed tick.before) :
    ∃ after : OwnershipPrefix runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after,
      CurrentRootCreation prior.custody.caps prior.custody.catalogue after.custody.caps after.custody.catalogue tick position ∧
      CustodyOwnershipStep after.custody.catalogue tick prior.custody.caps.family after.custody.caps.family := by
  obtain ⟨afterCaps, afterCatalogue, state, coverage, valid, names, labels, update, included, origin, receipt⟩ :=
    actual_primitive_staging_creation_source_catalogued namespaceLaws descriptors aliases accounts lifetimes objects
      liveMetadata types lookup journal dataLookup cwdLookup selected action present authority mkdir
      prior.custody.namespaceState prior.custody.names shape count prior.custody.history prior.custody.catalogue
      prior.custody.coverage prior.custody.valid
  have actual := selected_filesystem_step tick action present
  have change := authority.namespace_delta namespaceLaws actual mkdir
  have ownership : CustodyOwnershipStep afterCatalogue tick prior.custody.caps.family afterCaps.family :=
    nonremoving_ownership_step afterCatalogue (creation_retains_bindings (before := tick.before.project engine) change (.inl mkdir))
      receipt.labels
  let next := prior.custody.advance_retained descriptors lifetimes references afterCaps afterCatalogue state names coverage valid
    update included action (by simp only [mkdir, RetainsDescriptors]; decide)
  exact ⟨prior.advance next included ownership, receipt, ownership⟩

-- §AR-host-boundary.interfaces: Keep the prior ownership consumer while the stronger
-- sibling retains its exact current catalogue choice and per-operation removal proof.
theorem staging_creation_ownership_prefix {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
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
    (prior : OwnershipPrefix runtime initial ticks hostUid dataObjects directories semantics foreignReferences processed tick.before) :
    Nonempty (OwnershipPrefix runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after) := by
  obtain ⟨next, choice, ownership⟩ := staging_creation_ownership_prefix_catalogued namespaceLaws descriptors aliases accounts lifetimes references objects liveMetadata types
      lookup journal dataLookup cwdLookup selected action present authority mkdir shape count prior
  exact ⟨next⟩

end LeanCage.Host.Kernel
