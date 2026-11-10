import FilesystemTraversalParents
import FilesystemCheckedParents
import FilesystemByteNamespaces
import FilesystemRunCreation

namespace LeanCage.Host.Kernel
open Filesystem

structure PrimitiveTraversalAuthority {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    (initial : World) (ticks : List (ActorTick runtime)) (tick : ActorTick runtime)
    (actor : ActorId) (engine : EngineState) (request : Request) (observed : Option Reply)
    (hostUid : Nat) (semantics : NameSemanticsView) where
  resources : PrimitiveTraversalParent runtime initial ticks tick actor engine request observed
  uid : resources.source.cursor.identity.1.toNat = hostUid
  information : Stat
  known : tick.before.shared.information resources.current.handle.object = some information
  trusted : Directories.trusted hostUid information = true
  names : (semantics.at tick.before.shared resources.current.handle.object).byteExact

-- §FS-host-boundary.ownership: In-progress public creation has a real earlier checked parent
-- and current supported operands, including all native/source actions between stat and mkdir.
theorem actual_primitive_traversal_authority {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat} {semantics : NameSemanticsView}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (raw : RawReferenceLifetimeContract kernel)
    (sdk : RuntimeDescriptorContract runtime) (accounts : AccountContract kernel hostUid)
    (metadata : GlobalAuthorityContract runtime child) (nativeMetadata : NativeMetadataContract native)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    (probes : LookupPrimitiveContract kernel.step kernel.interference semantics)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    (authorityProfile : NativeAuthorityProfile native ticks hostUid) (lookupProfile : NativeLookupProfile native ticks hostUid)
    {prior last : Processes} {callers next : NativeProcesses}
    (recording : NativeExternalJournal process child native hostUid prior callers ticks last next)
    {backend : NativeAuthorityJournal recording}
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    (selected : ticks[position]? = some tick) (present : tick.before.actors actor = some engine)
    {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial ticks tick actor engine request observed)
    (source : TraversalCall adapter.occurrence.logicalBefore request) (mkdir : request.op = .mkdirAt) :
    Nonempty (PrimitiveTraversalAuthority runtime initial ticks tick actor engine request observed hostUid semantics) := by
  obtain ⟨resources⟩ := primitive_traversal_parent descriptors adapter source mkdir
  have uid := sampled_uid_is_host accounts resources.identity
  cases uid
  have live : engine.references resources.source.cursor.cursor.current.fd = some resources.current.handle := resources.current.live
  obtain ⟨interval, sameHandle, sameOrdinal⟩ := checked_parent_interval_owned (backend := backend) descriptors lifetimes references raw sdk accounts
    journal recording selected present resources.current live resources.current.earlier
  have member : resources.source.cursor.cursor.current.fd ∈ Lookup.parents request := by
    have operation := resources.source.cursor.cursor.operation
    exact (congrArg (fun operation => resources.source.cursor.cursor.current.fd ∈ Lookup.parents operation) operation).mpr
      (by simp [Lookup.parents])
  have earlier : interval.sample.ordinal < resources.adapter.occurrence.rawBefore.length := by
    rw [sameOrdinal]
    exact resources.parentBeforeGuard
  obtain ⟨information, known, trusted, names⟩ := checked_parent_comparison lifetimes metadata nativeMetadata lookup
    probes journal authorityProfile lookupProfile interval resources.adapter (.inr (.inl mkdir))
    resources.source.cursor.cursor.current.fd member interval.parent interval.reference rfl earlier
  exact ⟨⟨resources, rfl, information, by simpa only [sameHandle] using known, trusted,
    by simpa only [sameHandle] using names⟩⟩

theorem PrimitiveTraversalAuthority.namespace_delta {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {hostUid : Nat} {semantics : NameSemanticsView} {dataObjects : ObjectId → Prop}
    (laws : ByteNamespaceContract kernel semantics dataObjects)
    {initial : World} {ticks : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (authority : PrimitiveTraversalAuthority runtime initial ticks tick actor engine request observed hostUid semantics)
    (actual : kernel.step (tick.before.project engine) request observed tick.after.shared) :
    DataChange dataObjects request (tick.before.project engine) tick.after.shared := by
  obtain ⟨mkdir, descriptor, mode, component, publicName⟩ := authority.resources.source.arguments
  apply laws.mutation _ _ _ _ actual (.inl mkdir)
  · simpa only [ComponentRequest, mkdir] using component
  · exact (congrArg (DirectoryOperands (tick.before.project engine))
      authority.resources.source.cursor.cursor.operation).mpr ⟨authority.resources.current.handle, authority.resources.current.live⟩
  · intro fd member handle live
    have sameFd : fd = authority.resources.source.cursor.cursor.current.fd := by
      simpa only [Lookup.parents, mkdir, descriptor, List.mem_singleton] using member
    subst fd
    have same : handle = authority.resources.current.handle := Option.some.inj (live.symm.trans authority.resources.current.live)
    subst handle
    exact authority.names

-- §FS-host-boundary.ownership: This actual source case keeps a created public directory
-- outside the private catalogue. Its parent role is derived from the same prior source history.
theorem actual_primitive_public_creation {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat} {semantics : NameSemanticsView}
    {dataObjects directories : ObjectId → Prop}
    (namespaceLaws : ByteNamespaceContract kernel semantics dataObjects)
    (descriptors : DescriptorContract kernel) (aliases : DirectoryAliasContract kernel)
    (accounts : AccountContract kernel hostUid) (lifetimes : LifetimeContract runtime)
    (objects : ObjectLifetimeContract runtime) (liveMetadata : LiveMetadataContract runtime child)
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
    {caps : Capabilities} {foreignReferences : ForeignReferences}
    (state : NamespaceCustody tick.before.shared caps hostUid initial.allocated dataObjects directories foreignReferences)
    (names : RegisteredRootNames caps semantics tick.before.shared)
    {leading trailing : List (ActorTick runtime)} {first : Family}
    (shape : ticks = leading ++ tick :: trailing) (count : leading.length = position)
    (prefixLabels : ScopeJournal runtime initial.allocated dataObjects semantics
      (Population.empty initial) first leading tick.before caps.family)
    (catalogue : Catalogue runtime ticks) (covered : catalogue.Covers caps) (valid : catalogue.Valid tick.before.shared) :
    NamespaceCustody tick.after.shared (caps.retain tick.after.shared) hostUid
      initial.allocated dataObjects directories foreignReferences ∧
      Catalogue.Covers catalogue (caps.retain tick.after.shared) ∧ Catalogue.Valid catalogue tick.after.shared ∧
      RegisteredRootNames (caps.retain tick.after.shared) semantics tick.after.shared ∧
      FamilyUpdate tick.before.shared caps.family (caps.retain tick.after.shared).family := by
  have actual := selected_filesystem_step tick action present
  have filesystem := selected_filesystem_action_family action
  have safe := selected_primitive_action_authority journal selected
  obtain ⟨mkdir, descriptor, mode, component, publicName⟩ := authority.resources.source.arguments
  have change := authority.namespace_delta namespaceLaws actual
  have allocation : ∀ object, tick.before.shared.allocated object = true → tick.after.shared.allocated object = true :=
    fun object => kernel.allocation_monotone (tick.before.project engine) tick.after.shared request observed object actual
  have publicParent := authority.resources.public_parent descriptors aliases lifetimes dataLookup cwdLookup
    journal selected present shape count prefixLabels
  have custody : NamespaceCustody tick.after.shared (caps.retain tick.after.shared) hostUid
      initial.allocated dataObjects directories foreignReferences := by
    rcases mkdir_delta_cases change mkdir with unchanged | committed
    · exact source_unchanged_mkdir_custody accounts objects liveMetadata actual filesystem safe mkdir state.project unchanged
    · obtain ⟨delta⟩ := committed
      have reference : (tick.before.project engine).handles request.first = some authority.resources.current.handle := by
        rw [descriptor]
        exact authority.resources.current.live
      have same : delta.parent = authority.resources.current.handle := Option.some.inj (delta.reference.symm.trans reference)
      have parentPublic : caps.family delta.parent.object = none := by rw [same]; exact publicParent
      exact source_created_public_directory_custody accounts objects liveMetadata actual filesystem safe mkdir
        state.project delta parentPublic
  exact ⟨custody, catalogue_retained_covers covered, catalogue_advance_valid valid allocation,
    filesystem_registered_root_names lookup filesystem safe state.registry names, .same⟩

end LeanCage.Host.Kernel
