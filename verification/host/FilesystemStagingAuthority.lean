import FilesystemCurrentBirth
import FilesystemStagingParents
import FilesystemCheckedParents
import FilesystemByteNamespaces
import FilesystemRunCreation
import FilesystemPublicParents

namespace LeanCage.Host.Kernel
open Filesystem

structure PrimitiveStagingAuthority {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    (initial : World) (ticks : List (ActorTick runtime)) (tick : ActorTick runtime)
    (actor : ActorId) (engine : EngineState) (request : Request) (observed : Option Reply)
    (hostUid : Nat) (semantics : NameSemanticsView) where
  resources : PrimitiveStagingParent runtime initial ticks tick actor engine request observed
  uid : resources.source.selection.parent.uid = hostUid
  information : Stat
  known : tick.before.shared.information resources.parent.directory.handle.object = some information
  trusted : Directories.trusted hostUid information = true
  names : (semantics.at tick.before.shared resources.parent.directory.handle.object).byteExact

-- §FS-host-boundary.ownership: The same current public parent is established by its actual
-- retained-CWD/source traversal; it is not a preparation premise or an independent FD role.
theorem PrimitiveStagingAuthority.public_parent {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {hostUid : Nat} {semantics : NameSemanticsView} {initialObjects : ObjectId → Bool} {dataObjects : ObjectId → Prop}
    (descriptors : DescriptorContract kernel) (aliases : DirectoryAliasContract kernel)
    (lifetimes : LifetimeContract runtime)
    (lookup : DynamicDataLookupContract kernel semantics initialObjects dataObjects)
    (cwdLookup : WorkingDirectoryContract kernel initialObjects dataObjects)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    (selected : ticks[position]? = some tick) (present : tick.before.actors actor = some engine)
    {leading trailing : List (ActorTick runtime)} {first family : Family}
    (shape : ticks = leading ++ tick :: trailing) (count : leading.length = position)
    (prefixLabels : ScopeJournal runtime initialObjects dataObjects semantics
      (Population.empty initial) first leading tick.before family)
    {request : Request} {observed : Option Reply}
    (authority : PrimitiveStagingAuthority runtime initial ticks tick actor engine request observed hostUid semantics) :
    family authority.resources.parent.directory.handle.object = none := by
  obtain ⟨handle, live, publicObject⟩ := Lowered.parent_history_public descriptors aliases lifetimes lookup cwdLookup
    journal selected present shape count prefixLabels authority.resources.selection.rawBefore.length
    authority.resources.source.source.source.target true authority.resources.selection.actual authority.resources.selectionLimit
  have same : handle = authority.resources.parent.directory.handle :=
    Option.some.inj (live.symm.trans authority.resources.parentAtSelection)
  simpa only [same] using publicObject

-- §FS-host-boundary.ownership: Both staging parent FDs come from the actual source selection.
-- Its earlier checked fstat and the same raw mkdir probe establish current authority/comparison.
theorem actual_primitive_staging_authority {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat} {semantics : NameSemanticsView}
    (descriptors : DescriptorContract kernel) (aliases : DirectoryAliasContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (raw : RawReferenceLifetimeContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (accounts : AccountContract kernel hostUid)
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
    (source : StagingCall adapter.occurrence.logicalBefore request) (mkdir : request.op = .mkdirAt) :
    Nonempty (PrimitiveStagingAuthority runtime initial ticks tick actor engine request observed hostUid semantics) := by
  obtain ⟨resources⟩ := primitive_staging_parent descriptors aliases adapter source mkdir
  have uid := sampled_uid_is_host accounts resources.parent.identity
  cases uid
  have current : engine.references resources.source.selection.parent.directory.fd =
      some resources.parent.directory.handle := resources.parent.directory.live
  obtain ⟨interval, sameHandle, sameOrdinal⟩ := checked_parent_interval_owned (backend := backend) descriptors lifetimes references raw sdk accounts
    journal recording selected present resources.parent.directory current resources.parent.directory.earlier
  have member : resources.source.child.container.fd ∈ Lookup.parents request := by
    exact (congrArg (fun operation => resources.source.child.container.fd ∈ Lookup.parents operation)
      resources.source.child.child.operation).mpr (by simp [Lookup.parents])
  have earlier : interval.sample.ordinal < resources.adapter.occurrence.rawBefore.length := by
    rw [sameOrdinal]
    exact resources.parentBeforeGuard
  have identity : resources.container.handle.object = interval.parent.object := by
    rw [sameHandle]
    exact resources.sameParent
  obtain ⟨information, known, trusted, names⟩ := checked_parent_comparison lifetimes metadata nativeMetadata lookup
    probes journal authorityProfile lookupProfile interval resources.adapter (.inr (.inl mkdir))
    resources.source.child.container.fd member resources.container.handle resources.container.live identity earlier
  exact ⟨⟨resources, rfl, information, by simpa only [sameHandle] using known, trusted,
    by simpa only [sameHandle] using names⟩⟩

-- §FS-host-boundary.ownership: These are the exact raw operation operands, not an assumed
-- staging-tree effect. Error/lost acknowledgements still use the same current namespace delta.
theorem PrimitiveStagingAuthority.namespace_delta {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {hostUid : Nat} {semantics : NameSemanticsView} {dataObjects : ObjectId → Prop}
    (laws : ByteNamespaceContract kernel semantics dataObjects)
    {initial : World} {ticks : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (authority : PrimitiveStagingAuthority runtime initial ticks tick actor engine request observed hostUid semantics)
    (actual : kernel.step (tick.before.project engine) request observed tick.after.shared)
    (mkdir : request.op = .mkdirAt) : DataChange dataObjects request (tick.before.project engine) tick.after.shared := by
  have source := authority.resources.source.child.child
  have components : ComponentRequest request := (congrArg ComponentRequest source.operation).mpr source.component
  have operands : DirectoryOperands (tick.before.project engine) request :=
    (congrArg (DirectoryOperands (tick.before.project engine)) source.operation).mpr
      ⟨authority.resources.container.handle, authority.resources.container.live⟩
  apply laws.mutation _ _ _ _ actual (.inl mkdir) components operands
  intro fd member handle live
  have sameFd : fd = authority.resources.source.child.container.fd := by
    have parents : Lookup.parents request = [authority.resources.source.child.container.fd] :=
      (congrArg Lookup.parents source.operation).trans rfl
    simpa only [parents, List.mem_singleton] using member
  subst fd
  have same := Option.some.inj (live.symm.trans authority.resources.container.live)
  subst handle
  simpa only [NameSemanticsView.at, Population.project, authority.resources.sameParent] using authority.names

-- §FS-host-boundary.ownership: This local fold case records the actual private staging birth,
-- including committed errors/loss. Public-parent labels come from the preceding source walk.
theorem actual_primitive_staging_creation_catalogued {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat} {semantics : NameSemanticsView}
    {dataObjects directories : ObjectId → Prop}
    (namespaceLaws : ByteNamespaceContract kernel semantics dataObjects)
    (accounts : AccountContract kernel hostUid) (lifetimes : LifetimeContract runtime)
    (objects : ObjectLifetimeContract runtime) (liveMetadata : LiveMetadataContract runtime child)
    (types : CreationTypeContract kernel directories)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState} {request : Request}
    {observed : Option Reply} (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (authority : PrimitiveStagingAuthority runtime initial ticks tick actor engine request observed hostUid semantics)
    (mkdir : request.op = .mkdirAt)
    {caps : Capabilities} {foreignReferences : ForeignReferences}
    (state : NamespaceCustody tick.before.shared caps hostUid initial.allocated dataObjects directories foreignReferences)
    (names : RegisteredRootNames caps semantics tick.before.shared)
    (publicParent : caps.family authority.resources.parent.directory.handle.object = none)
    (catalogue : Catalogue runtime ticks) (covered : catalogue.Covers caps) (valid : catalogue.Valid tick.before.shared) :
    ∃ (afterCaps : Capabilities) (afterCatalogue : Catalogue runtime ticks),
      NamespaceCustody tick.after.shared afterCaps hostUid initial.allocated dataObjects directories foreignReferences ∧
      Catalogue.Covers afterCatalogue afterCaps ∧ Catalogue.Valid afterCatalogue tick.after.shared ∧
      RegisteredRootNames afterCaps semantics tick.after.shared ∧
      ExistingLabels tick.before.shared tick.after.shared caps.family afterCaps.family ∧
      FamilyUpdate tick.before.shared caps.family afterCaps.family ∧
      (∀ record ∈ catalogue, record ∈ afterCatalogue) ∧
      (afterCaps = caps.retain tick.after.shared ∨
        ∃ object, Nonempty (RootBirth runtime ticks
          ⟨actor, object, authority.resources.parent.directory.handle.object, request.left⟩) ∧
          afterCaps = caps.addRoot ⟨actor, object, authority.resources.parent.directory.handle.object, request.left⟩) ∧
      CurrentRootCreation caps catalogue afterCaps afterCatalogue tick position := by
  have actual := selected_filesystem_step tick action present
  have filesystem := selected_filesystem_action_family action
  have safe := selected_primitive_action_authority journal selected
  have change := authority.namespace_delta namespaceLaws actual mkdir
  have allocation : ∀ object, tick.before.shared.allocated object = true → tick.after.shared.allocated object = true :=
    fun object => kernel.allocation_monotone (tick.before.project engine) tick.after.shared request observed object actual
  rcases mkdir_delta_cases change mkdir with unchanged | committed
  · exact ⟨caps.retain tick.after.shared, catalogue,
      source_unchanged_mkdir_custody accounts objects liveMetadata actual filesystem safe mkdir state.project unchanged,
      catalogue_retained_covers covered, catalogue_advance_valid valid allocation,
      filesystem_registered_root_names lookup filesystem safe state.registry names,
      unchanged_existing_labels _ _ _, .same, (by intro record member; exact member), .inl rfl, .retained rfl rfl unchanged⟩
  · obtain ⟨delta⟩ := committed
    have descriptor := congrArg Request.first authority.resources.source.child.child.operation
    have mode := congrArg Request.second authority.resources.source.child.child.operation
    have component : Directories.component request.left = true := by
      simpa only [authority.resources.source.child.child.operation] using authority.resources.source.child.child.component
    have reserved : PrivateNames.reservedBytes request.left = true := by
      rw [authority.resources.source.child.child.operation]
      exact private_prefix_reserved _
    have reference : (tick.before.project engine).handles request.first = some authority.resources.container.handle := by
      rw [descriptor]
      exact authority.resources.container.live
    have same : delta.parent = authority.resources.container.handle := Option.some.inj (delta.reference.symm.trans reference)
    have parentObject : delta.parent.object = authority.resources.parent.directory.handle.object :=
      (congrArg Handle.object same).trans authority.resources.sameParent
    let birth := private_root_birth_data selected action present mkdir mode component reserved delta
    have young := root_birth_not_initial lifetimes journal birth
    let root : PrivateRoot := ⟨actor, delta.object, delta.parent.object, request.left⟩
    have parentPublic : caps.family delta.parent.object = none := by rw [parentObject]; exact publicParent
    have parentKnown : tick.before.shared.information delta.parent.object = some authority.information := by
      rw [parentObject]
      exact authority.known
    have parentNames : (semantics.at tick.before.shared delta.parent.object).byteExact := by
      rw [parentObject]
      exact authority.names
    have currentState := source_created_directory_custody accounts objects liveMetadata types actual filesystem safe
      mkdir mode actor state.project delta young parentPublic reserved parentKnown authority.trusted
    refine ⟨caps.addRoot root, Sigma.mk root birth :: catalogue, currentState, catalogue_add_covers covered birth,
      catalogue_add_valid lifetimes birth valid,
      created_registered_root_names lookup filesystem safe delta actor state.registry names parentNames,
      set_family_existing_labels delta.fresh, .fresh delta.object delta.object delta.fresh,
      (by intro record member; exact List.mem_cons_of_mem _ member), .inr ⟨delta.object, ?_, ?_⟩,
      .created root birth rfl rfl rfl rfl⟩
    · simpa only [root, parentObject] using (show Nonempty (RootBirth runtime ticks root) from ⟨birth⟩)
    · simp only [root, parentObject]

-- §AR-host-boundary.interfaces: Preserve the earlier current-birth receipt; the catalogued
-- sibling above additionally fixes the exact inserted record and excludes extra records.
theorem actual_primitive_staging_creation_current {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat} {semantics : NameSemanticsView}
    {dataObjects directories : ObjectId → Prop}
    (namespaceLaws : ByteNamespaceContract kernel semantics dataObjects)
    (accounts : AccountContract kernel hostUid) (lifetimes : LifetimeContract runtime)
    (objects : ObjectLifetimeContract runtime) (liveMetadata : LiveMetadataContract runtime child)
    (types : CreationTypeContract kernel directories)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState} {request : Request}
    {observed : Option Reply} (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (authority : PrimitiveStagingAuthority runtime initial ticks tick actor engine request observed hostUid semantics)
    (mkdir : request.op = .mkdirAt)
    {caps : Capabilities} {foreignReferences : ForeignReferences}
    (state : NamespaceCustody tick.before.shared caps hostUid initial.allocated dataObjects directories foreignReferences)
    (names : RegisteredRootNames caps semantics tick.before.shared)
    (publicParent : caps.family authority.resources.parent.directory.handle.object = none)
    (catalogue : Catalogue runtime ticks) (covered : catalogue.Covers caps) (valid : catalogue.Valid tick.before.shared) :
    ∃ (afterCaps : Capabilities) (afterCatalogue : Catalogue runtime ticks),
      NamespaceCustody tick.after.shared afterCaps hostUid initial.allocated dataObjects directories foreignReferences ∧
      Catalogue.Covers afterCatalogue afterCaps ∧ Catalogue.Valid afterCatalogue tick.after.shared ∧
      RegisteredRootNames afterCaps semantics tick.after.shared ∧
      ExistingLabels tick.before.shared tick.after.shared caps.family afterCaps.family ∧
      FamilyUpdate tick.before.shared caps.family afterCaps.family ∧
      (∀ record ∈ catalogue, record ∈ afterCatalogue) ∧
      (afterCaps = caps.retain tick.after.shared ∨
        ∃ object, Nonempty (RootBirth runtime ticks
          ⟨actor, object, authority.resources.parent.directory.handle.object, request.left⟩) ∧
          afterCaps = caps.addRoot ⟨actor, object, authority.resources.parent.directory.handle.object, request.left⟩) ∧
      (afterCaps = caps.retain tick.after.shared ∨
        ∃ (root : PrivateRoot) (birth : RootBirth runtime ticks root),
          birth.tick = tick ∧ birth.position = position ∧ Sigma.mk root birth ∈ afterCatalogue ∧
            afterCaps = caps.addRoot root) := by
  obtain ⟨afterCaps, afterCatalogue, custody, coverage, currentValid, comparisons, labels, flow, included, origin, choice⟩ :=
    actual_primitive_staging_creation_catalogued namespaceLaws accounts lifetimes objects liveMetadata types lookup journal
      selected action present authority mkdir state names publicParent catalogue covered valid
  exact ⟨afterCaps, afterCatalogue, custody, coverage, currentValid, comparisons, labels, flow, included, origin,
    choice.receipt⟩

-- §AR-host-boundary.interfaces: Preserve the prior staging flow interface; the current
-- producer above also retains the exact global birth position and catalogue member.
theorem actual_primitive_staging_creation_with_flow {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat} {semantics : NameSemanticsView}
    {dataObjects directories : ObjectId → Prop}
    (namespaceLaws : ByteNamespaceContract kernel semantics dataObjects)
    (accounts : AccountContract kernel hostUid) (lifetimes : LifetimeContract runtime)
    (objects : ObjectLifetimeContract runtime) (liveMetadata : LiveMetadataContract runtime child)
    (types : CreationTypeContract kernel directories)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState} {request : Request}
    {observed : Option Reply} (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (authority : PrimitiveStagingAuthority runtime initial ticks tick actor engine request observed hostUid semantics)
    (mkdir : request.op = .mkdirAt)
    {caps : Capabilities} {foreignReferences : ForeignReferences}
    (state : NamespaceCustody tick.before.shared caps hostUid initial.allocated dataObjects directories foreignReferences)
    (names : RegisteredRootNames caps semantics tick.before.shared)
    (publicParent : caps.family authority.resources.parent.directory.handle.object = none)
    (catalogue : Catalogue runtime ticks) (covered : catalogue.Covers caps) (valid : catalogue.Valid tick.before.shared) :
    ∃ (afterCaps : Capabilities) (afterCatalogue : Catalogue runtime ticks),
      NamespaceCustody tick.after.shared afterCaps hostUid initial.allocated dataObjects directories foreignReferences ∧
      Catalogue.Covers afterCatalogue afterCaps ∧ Catalogue.Valid afterCatalogue tick.after.shared ∧
      RegisteredRootNames afterCaps semantics tick.after.shared ∧
      ExistingLabels tick.before.shared tick.after.shared caps.family afterCaps.family ∧
      FamilyUpdate tick.before.shared caps.family afterCaps.family ∧
      (∀ record ∈ catalogue, record ∈ afterCatalogue) ∧
      (afterCaps = caps.retain tick.after.shared ∨
        ∃ object, Nonempty (RootBirth runtime ticks
          ⟨actor, object, authority.resources.parent.directory.handle.object, request.left⟩) ∧
          afterCaps = caps.addRoot ⟨actor, object, authority.resources.parent.directory.handle.object, request.left⟩) := by
  obtain ⟨afterCaps, afterCatalogue, custody, coverage, currentValid, comparisons, labels, flow, included, origin, receipt⟩ :=
    actual_primitive_staging_creation_current namespaceLaws accounts lifetimes objects liveMetadata types lookup journal
      selected action present authority mkdir state names publicParent catalogue covered valid
  exact ⟨afterCaps, afterCatalogue, custody, coverage, currentValid, comparisons, labels, flow, included, origin⟩

-- §AR-host-boundary.interfaces: Preserve the original local-case interface while the
-- stronger sibling retains its exact source-owned scope update.
theorem actual_primitive_staging_creation {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat} {semantics : NameSemanticsView}
    {dataObjects directories : ObjectId → Prop}
    (namespaceLaws : ByteNamespaceContract kernel semantics dataObjects)
    (accounts : AccountContract kernel hostUid) (lifetimes : LifetimeContract runtime)
    (objects : ObjectLifetimeContract runtime) (liveMetadata : LiveMetadataContract runtime child)
    (types : CreationTypeContract kernel directories)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState} {request : Request}
    {observed : Option Reply} (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (authority : PrimitiveStagingAuthority runtime initial ticks tick actor engine request observed hostUid semantics)
    (mkdir : request.op = .mkdirAt)
    {caps : Capabilities} {foreignReferences : ForeignReferences}
    (state : NamespaceCustody tick.before.shared caps hostUid initial.allocated dataObjects directories foreignReferences)
    (names : RegisteredRootNames caps semantics tick.before.shared)
    (publicParent : caps.family authority.resources.parent.directory.handle.object = none)
    (catalogue : Catalogue runtime ticks) (covered : catalogue.Covers caps) (valid : catalogue.Valid tick.before.shared) :
    ∃ (afterCaps : Capabilities) (afterCatalogue : Catalogue runtime ticks),
      NamespaceCustody tick.after.shared afterCaps hostUid initial.allocated dataObjects directories foreignReferences ∧
      Catalogue.Covers afterCatalogue afterCaps ∧ Catalogue.Valid afterCatalogue tick.after.shared ∧
      RegisteredRootNames afterCaps semantics tick.after.shared ∧
      ExistingLabels tick.before.shared tick.after.shared caps.family afterCaps.family ∧
      (afterCaps = caps.retain tick.after.shared ∨
        ∃ object, Nonempty (RootBirth runtime ticks
          ⟨actor, object, authority.resources.parent.directory.handle.object, request.left⟩) ∧
          afterCaps = caps.addRoot ⟨actor, object, authority.resources.parent.directory.handle.object, request.left⟩) := by
  obtain ⟨afterCaps, afterCatalogue, custody, coverage, currentValid, comparisons, labels, flow, included, origin⟩ :=
    actual_primitive_staging_creation_with_flow namespaceLaws accounts lifetimes objects liveMetadata types lookup journal
      selected action present authority mkdir state names publicParent catalogue covered valid
  exact ⟨afterCaps, afterCatalogue, custody, coverage, currentValid, comparisons, labels, origin⟩

-- §FS-host-boundary.ownership: The source-selected staging parent retains the exact
-- catalogue transition, same current birth tick and owned parent selection.
theorem actual_primitive_staging_creation_source_catalogued {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat} {semantics : NameSemanticsView}
    {dataObjects directories : ObjectId → Prop}
    (namespaceLaws : ByteNamespaceContract kernel semantics dataObjects)
    (descriptors : DescriptorContract kernel) (aliases : DirectoryAliasContract kernel)
    (accounts : AccountContract kernel hostUid) (lifetimes : LifetimeContract runtime)
    (objects : ObjectLifetimeContract runtime) (liveMetadata : LiveMetadataContract runtime child)
    (types : CreationTypeContract kernel directories)
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
    {caps : Capabilities} {foreignReferences : ForeignReferences}
    (state : NamespaceCustody tick.before.shared caps hostUid initial.allocated dataObjects directories foreignReferences)
    (names : RegisteredRootNames caps semantics tick.before.shared)
    {leading trailing : List (ActorTick runtime)} {first : Family}
    (shape : ticks = leading ++ tick :: trailing) (count : leading.length = position)
    (prefixLabels : ScopeJournal runtime initial.allocated dataObjects semantics
      (Population.empty initial) first leading tick.before caps.family)
    (catalogue : Catalogue runtime ticks) (covered : catalogue.Covers caps) (valid : catalogue.Valid tick.before.shared) :
    ∃ (afterCaps : Capabilities) (afterCatalogue : Catalogue runtime ticks),
      NamespaceCustody tick.after.shared afterCaps hostUid initial.allocated dataObjects directories foreignReferences ∧
      Catalogue.Covers afterCatalogue afterCaps ∧ Catalogue.Valid afterCatalogue tick.after.shared ∧
      RegisteredRootNames afterCaps semantics tick.after.shared ∧
      ExistingLabels tick.before.shared tick.after.shared caps.family afterCaps.family ∧
      FamilyUpdate tick.before.shared caps.family afterCaps.family ∧
      (∀ record ∈ catalogue, record ∈ afterCatalogue) ∧
      (afterCaps = caps.retain tick.after.shared ∨
        ∃ object, Nonempty (RootBirth runtime ticks
          ⟨actor, object, authority.resources.parent.directory.handle.object, request.left⟩) ∧
          afterCaps = caps.addRoot ⟨actor, object, authority.resources.parent.directory.handle.object, request.left⟩) ∧
      CurrentRootCreation caps catalogue afterCaps afterCatalogue tick position := by
  have publicParent := authority.public_parent descriptors aliases lifetimes dataLookup cwdLookup
    journal selected present shape count prefixLabels
  exact actual_primitive_staging_creation_catalogued namespaceLaws accounts lifetimes objects liveMetadata types lookup
    journal selected action present authority mkdir state names publicParent catalogue covered valid

theorem actual_primitive_staging_creation_source_current {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat} {semantics : NameSemanticsView}
    {dataObjects directories : ObjectId → Prop}
    (namespaceLaws : ByteNamespaceContract kernel semantics dataObjects)
    (descriptors : DescriptorContract kernel) (aliases : DirectoryAliasContract kernel)
    (accounts : AccountContract kernel hostUid) (lifetimes : LifetimeContract runtime)
    (objects : ObjectLifetimeContract runtime) (liveMetadata : LiveMetadataContract runtime child)
    (types : CreationTypeContract kernel directories)
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
    {caps : Capabilities} {foreignReferences : ForeignReferences}
    (state : NamespaceCustody tick.before.shared caps hostUid initial.allocated dataObjects directories foreignReferences)
    (names : RegisteredRootNames caps semantics tick.before.shared)
    {leading trailing : List (ActorTick runtime)} {first : Family}
    (shape : ticks = leading ++ tick :: trailing) (count : leading.length = position)
    (prefixLabels : ScopeJournal runtime initial.allocated dataObjects semantics
      (Population.empty initial) first leading tick.before caps.family)
    (catalogue : Catalogue runtime ticks) (covered : catalogue.Covers caps) (valid : catalogue.Valid tick.before.shared) :
    ∃ (afterCaps : Capabilities) (afterCatalogue : Catalogue runtime ticks),
      NamespaceCustody tick.after.shared afterCaps hostUid initial.allocated dataObjects directories foreignReferences ∧
      Catalogue.Covers afterCatalogue afterCaps ∧ Catalogue.Valid afterCatalogue tick.after.shared ∧
      RegisteredRootNames afterCaps semantics tick.after.shared ∧
      ExistingLabels tick.before.shared tick.after.shared caps.family afterCaps.family ∧
      FamilyUpdate tick.before.shared caps.family afterCaps.family ∧
      (∀ record ∈ catalogue, record ∈ afterCatalogue) ∧
      (afterCaps = caps.retain tick.after.shared ∨
        ∃ object, Nonempty (RootBirth runtime ticks
          ⟨actor, object, authority.resources.parent.directory.handle.object, request.left⟩) ∧
          afterCaps = caps.addRoot ⟨actor, object, authority.resources.parent.directory.handle.object, request.left⟩) ∧
      (afterCaps = caps.retain tick.after.shared ∨
        ∃ (root : PrivateRoot) (birth : RootBirth runtime ticks root),
          birth.tick = tick ∧ birth.position = position ∧ Sigma.mk root birth ∈ afterCatalogue ∧
            afterCaps = caps.addRoot root) := by
  have publicParent := authority.public_parent descriptors aliases lifetimes dataLookup cwdLookup
    journal selected present shape count prefixLabels
  exact actual_primitive_staging_creation_current namespaceLaws accounts lifetimes objects liveMetadata types lookup
    journal selected action present authority mkdir state names publicParent catalogue covered valid

theorem actual_primitive_staging_creation_from_source {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat} {semantics : NameSemanticsView}
    {dataObjects directories : ObjectId → Prop}
    (namespaceLaws : ByteNamespaceContract kernel semantics dataObjects)
    (descriptors : DescriptorContract kernel) (aliases : DirectoryAliasContract kernel)
    (accounts : AccountContract kernel hostUid) (lifetimes : LifetimeContract runtime)
    (objects : ObjectLifetimeContract runtime) (liveMetadata : LiveMetadataContract runtime child)
    (types : CreationTypeContract kernel directories)
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
    {caps : Capabilities} {foreignReferences : ForeignReferences}
    (state : NamespaceCustody tick.before.shared caps hostUid initial.allocated dataObjects directories foreignReferences)
    (names : RegisteredRootNames caps semantics tick.before.shared)
    {leading trailing : List (ActorTick runtime)} {first : Family}
    (shape : ticks = leading ++ tick :: trailing) (count : leading.length = position)
    (prefixLabels : ScopeJournal runtime initial.allocated dataObjects semantics
      (Population.empty initial) first leading tick.before caps.family)
    (catalogue : Catalogue runtime ticks) (covered : catalogue.Covers caps) (valid : catalogue.Valid tick.before.shared) :
    ∃ (afterCaps : Capabilities) (afterCatalogue : Catalogue runtime ticks),
      NamespaceCustody tick.after.shared afterCaps hostUid initial.allocated dataObjects directories foreignReferences ∧
      Catalogue.Covers afterCatalogue afterCaps ∧ Catalogue.Valid afterCatalogue tick.after.shared ∧
      RegisteredRootNames afterCaps semantics tick.after.shared ∧
      ExistingLabels tick.before.shared tick.after.shared caps.family afterCaps.family ∧
      FamilyUpdate tick.before.shared caps.family afterCaps.family ∧
      (∀ record ∈ catalogue, record ∈ afterCatalogue) ∧
      (afterCaps = caps.retain tick.after.shared ∨
        ∃ object, Nonempty (RootBirth runtime ticks
          ⟨actor, object, authority.resources.parent.directory.handle.object, request.left⟩) ∧
          afterCaps = caps.addRoot ⟨actor, object, authority.resources.parent.directory.handle.object, request.left⟩) := by
  have publicParent := authority.public_parent descriptors aliases lifetimes dataLookup cwdLookup
    journal selected present shape count prefixLabels
  exact actual_primitive_staging_creation_with_flow namespaceLaws accounts lifetimes objects liveMetadata types lookup
    journal selected action present authority mkdir state names publicParent catalogue covered valid

end LeanCage.Host.Kernel
