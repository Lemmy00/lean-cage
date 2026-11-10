import FilesystemCustodyState
import FilesystemCreationOwnership
import FilesystemRegisteredCustody

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: The actual root creation extends the complete joint state,
-- preserving native references/CWD and every historical birth cut on the SAME processed prefix.
theorem run_creation_custody_state_catalogued {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
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
    {nativeCurrent : NativeProcesses}
    (prior : CustodyState runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences processed tick.before nativeCurrent)
    (positionCount : processed.length = position) :
    ∃ updated : CustodyState runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after nativeCurrent,
      CurrentRootCreation prior.source.custody.caps prior.source.custody.catalogue
        updated.source.custody.caps updated.source.custody.catalogue tick position := by
  obtain ⟨next, choice, ownership⟩ := run_creation_ownership_prefix_catalogued (backend := backend) namespaceLaws descriptors lifetimes
      references raw sdk accounts objects liveMetadata types
      metadata nativeMetadata lookup probes journal anchor anchorLookup anchors authorityProfile lookupProfile
      recording selected action present source prior.source
  have notLaunch : ∀ owner references closeExec directory, tick.action ≠ .launch owner references closeExec directory := by
    intro owner references closeExec directory impossible
    rw [impossible] at action
    cases action
  have labels : ExistingLabels tick.before.shared tick.after.shared
      prior.source.custody.caps.family next.custody.caps.family :=
    fun object allocated => .inl (choice.labels object allocated)
  exact ⟨prior.application sdk lifetimes next notLaunch labels choice.included
    (choice.catalogue_members positionCount next.custody.namespaceState.registry) ownership, choice⟩

-- §FS-host-boundary.ownership: Preserve the exact current creation choice and source registry.

theorem run_creation_custody_state {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
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
    {nativeCurrent : NativeProcesses}
    (prior : CustodyState runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences processed tick.before nativeCurrent)
    (positionCount : processed.length = position) :
    Nonempty (CustodyState runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after nativeCurrent) := by
  obtain ⟨updated, choice⟩ := run_creation_custody_state_catalogued (backend := backend) namespaceLaws descriptors lifetimes references raw sdk accounts objects liveMetadata types metadata nativeMetadata lookup probes journal anchor anchorLookup anchors authorityProfile lookupProfile recording selected action present source prior positionCount
  exact ⟨updated⟩

-- §FS-host-boundary.ownership: Preserve the exact current creation choice and source registry.

theorem run_creation_custody_state_registered {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
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
    {nativeCurrent : NativeProcesses}
    (prior : RegisteredCustodyState runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences processed tick.before nativeCurrent)
    (positionCount : processed.length = position) :
    Nonempty (RegisteredCustodyState runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after nativeCurrent) := by
  obtain ⟨updated, choice⟩ := run_creation_custody_state_catalogued (backend := backend) namespaceLaws descriptors lifetimes references raw sdk accounts objects liveMetadata types metadata nativeMetadata lookup probes journal anchor anchorLookup anchors authorityProfile lookupProfile recording selected action present source prior.current positionCount
  exact ⟨prior.creation updated (by simpa only [positionCount] using choice)⟩

-- §FS-host-boundary.ownership: Preserve the exact current creation choice and source registry.

theorem staging_creation_custody_state_catalogued {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
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
    {nativeCurrent : NativeProcesses}
    (prior : CustodyState runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences processed tick.before nativeCurrent)
    (sdk : RuntimeDescriptorContract runtime) :
    ∃ updated : CustodyState runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after nativeCurrent,
      CurrentRootCreation prior.source.custody.caps prior.source.custody.catalogue
        updated.source.custody.caps updated.source.custody.catalogue tick position := by
  obtain ⟨next, choice, ownership⟩ := staging_creation_ownership_prefix_catalogued namespaceLaws descriptors aliases
      accounts lifetimes references objects liveMetadata types
      lookup journal dataLookup cwdLookup selected action present authority mkdir shape count prior.source
  have notLaunch : ∀ owner references closeExec directory, tick.action ≠ .launch owner references closeExec directory := by
    intro owner references closeExec directory impossible
    rw [impossible] at action
    cases action
  have labels : ExistingLabels tick.before.shared tick.after.shared
      prior.source.custody.caps.family next.custody.caps.family :=
    fun object allocated => .inl (choice.labels object allocated)
  exact ⟨prior.application sdk lifetimes next notLaunch labels choice.included
    (choice.catalogue_members count next.custody.namespaceState.registry) ownership, choice⟩

-- §FS-host-boundary.ownership: Preserve the exact current creation choice and source registry.

theorem staging_creation_custody_state {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
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
    {nativeCurrent : NativeProcesses}
    (prior : CustodyState runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences processed tick.before nativeCurrent)
    (sdk : RuntimeDescriptorContract runtime) :
    Nonempty (CustodyState runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after nativeCurrent) := by
  obtain ⟨updated, choice⟩ := staging_creation_custody_state_catalogued namespaceLaws descriptors aliases accounts lifetimes references objects liveMetadata types lookup journal dataLookup cwdLookup selected action present authority mkdir shape count prior sdk
  exact ⟨updated⟩

-- §FS-host-boundary.ownership: Preserve the exact current creation choice and source registry.

theorem staging_creation_custody_state_registered {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
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
    {nativeCurrent : NativeProcesses}
    (prior : RegisteredCustodyState runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences processed tick.before nativeCurrent)
    (sdk : RuntimeDescriptorContract runtime) :
    Nonempty (RegisteredCustodyState runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after nativeCurrent) := by
  obtain ⟨updated, choice⟩ := staging_creation_custody_state_catalogued namespaceLaws descriptors aliases accounts lifetimes references objects liveMetadata types lookup journal dataLookup cwdLookup selected action present authority mkdir shape count prior.current sdk
  exact ⟨prior.creation updated (by simpa only [count] using choice)⟩
end LeanCage.Host.Kernel
