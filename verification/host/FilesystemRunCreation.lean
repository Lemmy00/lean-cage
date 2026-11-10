import FilesystemCurrentBirth
import FilesystemCreationState
import FilesystemAnchorHistory
import FilesystemBoundaryComparison
import FilesystemScopeJournal

namespace LeanCage.Host.Kernel
open Filesystem

private def filesystemTag : Program.Event → Bool
  | .returned (.filesystem _) _ | .lost (.filesystem _) => true
  | _ => false

private theorem filesystem_event_family {action : ActorAction} {actor : ActorId}
    {request : Request} {observed : Option Reply}
    (selected : action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed))) :
    actionFamily action = .filesystem := by
  have tagged := congrArg (Option.map filesystemTag) selected
  cases action with
  | launch | foreign | retire | nativeRetire => cases selected
  | returned owner effect reply =>
    cases effect <;> try rfl
    all_goals
      by_cases same : actor = owner <;> cases observed <;>
        simp [ActorAction.eventFor, same, Program.filesystemPrefixEvent, filesystemTag] at tagged

  | lost owner effect =>
    cases effect <;> try rfl
    all_goals
      by_cases same : actor = owner <;> cases observed <;>
        simp [ActorAction.eventFor, same, Program.filesystemPrefixEvent, filesystemTag] at tagged

theorem selected_filesystem_action_family {action : ActorAction} {actor : ActorId}
    {request : Request} {observed : Option Reply}
    (selected : action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed))) :
    actionFamily action = .filesystem := filesystem_event_family selected

-- §FS-host-boundary.ownership: This is the actual run/validator mkdir case of the global
-- source fold. Its inputs are prior induction state and individual primitive/platform laws.
theorem actual_primitive_run_creation_catalogued {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
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
    {prior last : Processes} {callers next : NativeProcesses}
    (recording : NativeExternalJournal process child native hostUid prior callers ticks last next)
    {backend : NativeAuthorityJournal recording}
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState} {request : Request}
    {observed : Option Reply} (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (source : PrimitiveRunParent runtime initial ticks tick actor engine request)
    {caps : Capabilities} {foreignReferences : ForeignReferences}
    (state : NamespaceCustody tick.before.shared caps hostUid initial.allocated dataObjects directories foreignReferences)
    (names : RegisteredRootNames caps semantics tick.before.shared)
    (catalogue : Catalogue runtime ticks) (covered : catalogue.Covers caps) (valid : catalogue.Valid tick.before.shared) :
    ∃ (afterCaps : Capabilities) (afterCatalogue : Catalogue runtime ticks),
      NamespaceCustody tick.after.shared afterCaps hostUid initial.allocated dataObjects directories foreignReferences ∧
      Catalogue.Covers afterCatalogue afterCaps ∧ Catalogue.Valid afterCatalogue tick.after.shared ∧
      RegisteredRootNames afterCaps semantics tick.after.shared ∧
      ExistingLabels tick.before.shared tick.after.shared caps.family afterCaps.family ∧
      FamilyUpdate tick.before.shared caps.family afterCaps.family ∧
      (∀ record ∈ catalogue, record ∈ afterCatalogue) ∧
      (afterCaps = caps.retain tick.after.shared ∨
        ∃ object, Nonempty (RootBirth runtime ticks ⟨actor, object, anchor.visible, request.left⟩) ∧
          afterCaps = caps.addRoot ⟨actor, object, anchor.visible, request.left⟩) ∧
      CurrentRootCreation caps catalogue afterCaps afterCatalogue tick position := by
  have actual := selected_filesystem_step tick action present
  have filesystem := filesystem_event_family action
  have safe := selected_primitive_action_authority journal selected
  have change := primitive_run_mkdir_delta (backend := backend) namespaceLaws descriptors lifetimes references raw sdk accounts
    metadata nativeMetadata lookup probes journal authorityProfile lookupProfile recording selected action present source
  have allocation : ∀ object, tick.before.shared.allocated object = true → tick.after.shared.allocated object = true :=
    fun object => kernel.allocation_monotone (tick.before.project engine) tick.after.shared request observed object actual
  rcases mkdir_delta_cases change source.mkdir with unchanged | committed
  · exact ⟨caps.retain tick.after.shared, catalogue,
      source_unchanged_mkdir_custody accounts objects liveMetadata actual filesystem safe source.mkdir state.project unchanged,
      catalogue_retained_covers covered, catalogue_advance_valid valid allocation,
      filesystem_registered_root_names lookup filesystem safe state.registry names,
      unchanged_existing_labels _ _ _, .same, (by intro record member; exact member), .inl rfl, .retained rfl rfl unchanged⟩
  · obtain ⟨delta⟩ := committed
    obtain ⟨parent, live, rawParent, parentObject, parentPublic⟩ := primitive_run_parent_anchor descriptors anchor anchorLookup
      source (fun ordinal reply before after sampled => system_anchor_source_snapshot anchors sampled) state.graph
    obtain ⟨currentParent, information, currentReference, currentRaw, known, trusted, exactNames,
      mkdir, mode, component, reserved⟩ := primitive_run_mkdir_safe_parent (backend := backend) descriptors lifetimes references raw sdk accounts
        metadata nativeMetadata lookup probes journal authorityProfile lookupProfile recording selected present source
    have currentSame : currentParent = parent := Option.some.inj (currentReference.symm.trans live)
    subst currentParent
    have deltaSame : delta.parent = parent := Option.some.inj (delta.reference.symm.trans live)
    let birth := primitive_run_root_birth_data source selected action present delta
    have young := root_birth_not_initial lifetimes journal birth
    let root : PrivateRoot := ⟨actor, delta.object, delta.parent.object, request.left⟩
    have publicParent : caps.family delta.parent.object = none := by simpa only [deltaSame] using parentPublic
    have parentKnown : tick.before.shared.information delta.parent.object = some information := by
      simpa only [deltaSame] using known
    have parentNames : (semantics.at tick.before.shared delta.parent.object).byteExact := by
      simpa only [deltaSame] using exactNames
    have currentState := source_created_directory_custody accounts objects liveMetadata types actual filesystem safe
      source.mkdir mode actor state.project delta young publicParent reserved parentKnown trusted
    refine ⟨caps.addRoot root, Sigma.mk root birth :: catalogue, currentState, catalogue_add_covers covered birth,
      catalogue_add_valid lifetimes birth valid,
      created_registered_root_names lookup filesystem safe delta actor state.registry names parentNames,
      set_family_existing_labels delta.fresh, .fresh delta.object delta.object delta.fresh,
      (by intro record member; exact List.mem_cons_of_mem _ member), .inr ⟨delta.object, ?_, ?_⟩,
      .created root birth rfl rfl rfl rfl⟩
    · have same : delta.parent.object = anchor.visible := (congrArg Handle.object deltaSame).trans parentObject
      simpa only [root, same] using (show Nonempty (RootBirth runtime ticks root) from ⟨birth⟩)
    · have same : delta.parent.object = anchor.visible := (congrArg Handle.object deltaSame).trans parentObject
      simp only [root, same]

-- §AR-host-boundary.interfaces: Preserve the earlier current-birth receipt; the catalogued
-- sibling above additionally fixes the exact inserted record and excludes extra records.
theorem actual_primitive_run_creation_current {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
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
    {prior last : Processes} {callers next : NativeProcesses}
    (recording : NativeExternalJournal process child native hostUid prior callers ticks last next)
    {backend : NativeAuthorityJournal recording}
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState} {request : Request}
    {observed : Option Reply} (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (source : PrimitiveRunParent runtime initial ticks tick actor engine request)
    {caps : Capabilities} {foreignReferences : ForeignReferences}
    (state : NamespaceCustody tick.before.shared caps hostUid initial.allocated dataObjects directories foreignReferences)
    (names : RegisteredRootNames caps semantics tick.before.shared)
    (catalogue : Catalogue runtime ticks) (covered : catalogue.Covers caps) (valid : catalogue.Valid tick.before.shared) :
    ∃ (afterCaps : Capabilities) (afterCatalogue : Catalogue runtime ticks),
      NamespaceCustody tick.after.shared afterCaps hostUid initial.allocated dataObjects directories foreignReferences ∧
      Catalogue.Covers afterCatalogue afterCaps ∧ Catalogue.Valid afterCatalogue tick.after.shared ∧
      RegisteredRootNames afterCaps semantics tick.after.shared ∧
      ExistingLabels tick.before.shared tick.after.shared caps.family afterCaps.family ∧
      FamilyUpdate tick.before.shared caps.family afterCaps.family ∧
      (∀ record ∈ catalogue, record ∈ afterCatalogue) ∧
      (afterCaps = caps.retain tick.after.shared ∨
        ∃ object, Nonempty (RootBirth runtime ticks ⟨actor, object, anchor.visible, request.left⟩) ∧
          afterCaps = caps.addRoot ⟨actor, object, anchor.visible, request.left⟩) ∧
      (afterCaps = caps.retain tick.after.shared ∨
        ∃ (root : PrivateRoot) (birth : RootBirth runtime ticks root),
          birth.tick = tick ∧ birth.position = position ∧ Sigma.mk root birth ∈ afterCatalogue ∧
            afterCaps = caps.addRoot root) := by
  obtain ⟨afterCaps, afterCatalogue, custody, coverage, currentValid, comparisons, labels, flow, included, origin, choice⟩ :=
    actual_primitive_run_creation_catalogued (backend := backend) namespaceLaws descriptors lifetimes references raw sdk accounts
      objects liveMetadata types metadata nativeMetadata lookup probes journal anchor anchorLookup anchors
      authorityProfile lookupProfile recording selected action present source state names catalogue covered valid
  exact ⟨afterCaps, afterCatalogue, custody, coverage, currentValid, comparisons, labels, flow, included, origin,
    choice.receipt⟩

-- §AR-host-boundary.interfaces: Keep the prior flow theorem's exact type while retaining
-- the stronger SAME-tick/position/catalogue receipt in the current source producer.
theorem actual_primitive_run_creation_with_flow {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
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
    {prior last : Processes} {callers next : NativeProcesses}
    (recording : NativeExternalJournal process child native hostUid prior callers ticks last next)
    {backend : NativeAuthorityJournal recording}
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState} {request : Request}
    {observed : Option Reply} (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (source : PrimitiveRunParent runtime initial ticks tick actor engine request)
    {caps : Capabilities} {foreignReferences : ForeignReferences}
    (state : NamespaceCustody tick.before.shared caps hostUid initial.allocated dataObjects directories foreignReferences)
    (names : RegisteredRootNames caps semantics tick.before.shared)
    (catalogue : Catalogue runtime ticks) (covered : catalogue.Covers caps) (valid : catalogue.Valid tick.before.shared) :
    ∃ (afterCaps : Capabilities) (afterCatalogue : Catalogue runtime ticks),
      NamespaceCustody tick.after.shared afterCaps hostUid initial.allocated dataObjects directories foreignReferences ∧
      Catalogue.Covers afterCatalogue afterCaps ∧ Catalogue.Valid afterCatalogue tick.after.shared ∧
      RegisteredRootNames afterCaps semantics tick.after.shared ∧
      ExistingLabels tick.before.shared tick.after.shared caps.family afterCaps.family ∧
      FamilyUpdate tick.before.shared caps.family afterCaps.family ∧
      (∀ record ∈ catalogue, record ∈ afterCatalogue) ∧
      (afterCaps = caps.retain tick.after.shared ∨
        ∃ object, Nonempty (RootBirth runtime ticks ⟨actor, object, anchor.visible, request.left⟩) ∧
          afterCaps = caps.addRoot ⟨actor, object, anchor.visible, request.left⟩) := by
  obtain ⟨afterCaps, afterCatalogue, custody, coverage, currentValid, comparisons, labels, flow, included, origin, receipt⟩ :=
    actual_primitive_run_creation_current (backend := backend) namespaceLaws descriptors lifetimes references raw sdk accounts
      objects liveMetadata types metadata nativeMetadata lookup probes journal anchor anchorLookup anchors
      authorityProfile lookupProfile recording selected action present source state names catalogue covered valid
  exact ⟨afterCaps, afterCatalogue, custody, coverage, currentValid, comparisons, labels, flow, included, origin⟩

-- §AR-host-boundary.interfaces: Preserve the existing local-case result; the sibling retains
-- its exact application scope update for the completed-prefix custody induction.
theorem actual_primitive_run_creation {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
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
    {prior last : Processes} {callers next : NativeProcesses}
    (recording : NativeExternalJournal process child native hostUid prior callers ticks last next)
    {backend : NativeAuthorityJournal recording}
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState} {request : Request}
    {observed : Option Reply} (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (source : PrimitiveRunParent runtime initial ticks tick actor engine request)
    {caps : Capabilities} {foreignReferences : ForeignReferences}
    (state : NamespaceCustody tick.before.shared caps hostUid initial.allocated dataObjects directories foreignReferences)
    (names : RegisteredRootNames caps semantics tick.before.shared)
    (catalogue : Catalogue runtime ticks) (covered : catalogue.Covers caps) (valid : catalogue.Valid tick.before.shared) :
    ∃ (afterCaps : Capabilities) (afterCatalogue : Catalogue runtime ticks),
      NamespaceCustody tick.after.shared afterCaps hostUid initial.allocated dataObjects directories foreignReferences ∧
      Catalogue.Covers afterCatalogue afterCaps ∧ Catalogue.Valid afterCatalogue tick.after.shared ∧
      RegisteredRootNames afterCaps semantics tick.after.shared ∧
      ExistingLabels tick.before.shared tick.after.shared caps.family afterCaps.family ∧
      (afterCaps = caps.retain tick.after.shared ∨
        ∃ object, Nonempty (RootBirth runtime ticks ⟨actor, object, anchor.visible, request.left⟩) ∧
          afterCaps = caps.addRoot ⟨actor, object, anchor.visible, request.left⟩) := by
  obtain ⟨afterCaps, afterCatalogue, custody, coverage, currentValid, comparisons, labels, flow, included, origin⟩ :=
    actual_primitive_run_creation_with_flow (backend := backend) namespaceLaws descriptors lifetimes references raw sdk accounts
      objects liveMetadata types metadata nativeMetadata lookup probes journal anchor anchorLookup anchors
      authorityProfile lookupProfile recording selected action present source state names catalogue covered valid
  exact ⟨afterCaps, afterCatalogue, custody, coverage, currentValid, comparisons, labels, origin⟩

end LeanCage.Host.Kernel
