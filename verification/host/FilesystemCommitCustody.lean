import FilesystemPublicationOwnership

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.publication: A real selected rename extends the complete constructed
-- custody/ownership/registration prefix. Error and lost observations retain either actual
-- no-change or actual commit; scope release follows the physical move, never an ACK guess.
theorem commit_registered_custody_from_authority_byte {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat} {semantics : NameSemanticsView}
    {dataObjects directories : ObjectId → Prop}
    (namespaceLaws : ByteNamespaceContract kernel semantics dataObjects)
    (namespaceFrames : ByteNamespaceFrameContract kernel semantics)
    (descriptors : DescriptorContract kernel) (aliases : DirectoryAliasContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (environment : InterferenceContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (accounts : AccountContract kernel hostUid) (objects : ObjectLifetimeContract runtime)
    (metadata : LiveMetadataContract runtime child)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {final : Population} {all processed : List (ActorTick runtime)}
    (mounts : MountContract kernel initial.allocated)
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {currentNative : NativeProcesses}
    (prior : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative)
    {trailing : List (ActorTick runtime)} (whole : all = processed ++ tick :: trailing)
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (authority : PrimitiveCommitAuthority runtime initial all tick actor engine request observed hostUid semantics)
    (moving : request.op = .renameNew) :
    ∃ root : CommitRootAt runtime authority.resources prior.current.source.custody.caps.family
        prior.current.source.custody.catalogue,
      ∃ updated : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
          foreignReferences (processed ++ [tick]) tick.after currentNative,
        updated.current.source.custody.catalogue = prior.current.source.custody.catalogue ∧
        ((tick.after.shared.entries = tick.before.shared.entries ∧
          updated.current.source.custody.caps = prior.current.source.custody.caps.retain tick.after.shared) ∨
        (Nonempty (CommitDelta authority.resources root.root.object) ∧
          updated.current.source.custody.caps = prior.current.source.custody.caps.published tick.after.shared root.root.object)) := by
  have selected : all[processed.length]? = some tick := by
    rw [whole, List.getElem?_append_right (by omega)]
    simp only [Nat.sub_self, List.getElem?_cons_zero]
  obtain ⟨root⟩ := primitive_commit_root_from_resources descriptors aliases lifetimes references environment
    mounts journal prior whole present authority.resources moving
  have actual := selected_filesystem_step tick action present
  have filesystem := selected_filesystem_action_family action
  have safe := selected_primitive_action_authority journal selected
  have requestSafe : AuthoritySafeRequest request := by intro setting; rw [moving] at setting; cases setting
  have change := authority.namespace_delta namespaceLaws actual moving
  have allocation : ∀ object, tick.before.shared.allocated object = true → tick.after.shared.allocated object = true :=
    fun object => kernel.allocation_monotone (tick.before.project engine) tick.after.shared request observed object actual
  have names := filesystem_registered_root_names lookup filesystem safe
    prior.current.source.custody.namespaceState.registry prior.current.source.custody.names
  have valid := catalogue_advance_valid prior.current.source.custody.valid allocation
  have retaining : RetainsDescriptors request.op := by rw [moving]; simp [RetainsDescriptors]
  have notLaunch : ∀ owner handles closeExec directory, tick.action ≠ .launch owner handles closeExec directory := by
    intro owner handles closeExec directory impossible
    rw [impossible] at action
    cases action
  have noRoot : ¬ Nonempty (PrimitiveRootUse runtime initial all tick) :=
    no_root_use_of_other_operation action (by rw [moving]; decide)
  rcases root.delta_cases change moving with unchanged | committed
  · have state := source_unchanged_filesystem_custody accounts objects metadata actual filesystem safe requestSafe
      prior.current.source.custody.namespaceState.project unchanged
    let next := prior.current.source.custody.advance_retained descriptors lifetimes references
      (prior.current.source.custody.caps.retain tick.after.shared) prior.current.source.custody.catalogue
      state names (catalogue_retained_covers prior.current.source.custody.coverage) valid .same
      (by intro record member; exact member) action retaining
    have ownership : CustodyOwnershipStep next.catalogue tick prior.current.source.custody.caps.family next.caps.family :=
      nonremoving_ownership_step _ (by intro parent name object bound; rw [unchanged]; exact bound)
        (by intro object allocated; rfl)
    let afterSource := prior.current.source.advance next (by intro record member; exact member) ownership
    let updated := prior.sourceStep sdk lifetimes afterSource notLaunch (unchanged_existing_labels _ _ _)
      rfl ownership noRoot
    exact ⟨root, updated, rfl, .inl ⟨unchanged, rfl⟩⟩
  · obtain ⟨committed⟩ := committed
    have state := source_published_namespace_custody accounts objects metadata root
      prior.current.source.custody.coverage prior.current.source.custody.valid
      prior.current.source.custody.namespaceState.project actual filesystem safe moving change committed
    have names : RegisteredRootNames (prior.current.source.custody.caps.published tick.after.shared root.root.object)
        semantics tick.after.shared := names
    let update : FamilyUpdate tick.before.shared prior.current.source.custody.caps.family
        (prior.current.source.custody.caps.published tick.after.shared root.root.object).family := .published root.root.object
    let next := prior.current.source.custody.advance_retained descriptors lifetimes references
      (prior.current.source.custody.caps.published tick.after.shared root.root.object) prior.current.source.custody.catalogue
      state names (catalogue_published_covers prior.current.source.custody.coverage) valid update
      (by intro record member; exact member) action retaining
    have ownership : CustodyOwnershipStep next.catalogue tick prior.current.source.custody.caps.family next.caps.family :=
      source_publication_ownership_step_byte namespaceFrames root actual action moving authority.byte_operands
    let afterSource := prior.current.source.advance next (by intro record member; exact member) ownership
    let updated := prior.sourceStep sdk lifetimes afterSource notLaunch update.existing rfl ownership noRoot
    exact ⟨root, updated, rfl, .inr ⟨⟨committed⟩, rfl⟩⟩

-- §AR-host-boundary.interfaces: Preserve the original logical-frame consumer.
theorem commit_registered_custody_from_authority {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat} {semantics : NameSemanticsView}
    {dataObjects directories : ObjectId → Prop}
    (namespaceLaws : ByteNamespaceContract kernel semantics dataObjects)
    (namespaceFrames : NamespaceContract kernel)
    (descriptors : DescriptorContract kernel) (aliases : DirectoryAliasContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    (environment : InterferenceContract kernel) (sdk : RuntimeDescriptorContract runtime)
    (accounts : AccountContract kernel hostUid) (objects : ObjectLifetimeContract runtime)
    (metadata : LiveMetadataContract runtime child)
    (lookup : LookupMutationContract (runtime := runtime) child native)
    {initial : World} {final : Population} {all processed : List (ActorTick runtime)}
    (mounts : MountContract kernel initial.allocated)
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {currentNative : NativeProcesses}
    (prior : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative)
    {trailing : List (ActorTick runtime)} (whole : all = processed ++ tick :: trailing)
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (authority : PrimitiveCommitAuthority runtime initial all tick actor engine request observed hostUid semantics)
    (moving : request.op = .renameNew) :
    ∃ root : CommitRootAt runtime authority.resources prior.current.source.custody.caps.family
        prior.current.source.custody.catalogue,
      ∃ updated : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
          foreignReferences (processed ++ [tick]) tick.after currentNative,
        updated.current.source.custody.catalogue = prior.current.source.custody.catalogue ∧
        ((tick.after.shared.entries = tick.before.shared.entries ∧
          updated.current.source.custody.caps = prior.current.source.custody.caps.retain tick.after.shared) ∨
        (Nonempty (CommitDelta authority.resources root.root.object) ∧
          updated.current.source.custody.caps = prior.current.source.custody.caps.published tick.after.shared root.root.object)) := by
  exact commit_registered_custody_from_authority_byte namespaceLaws (namespaceFrames.byteFrames semantics)
    descriptors aliases lifetimes references environment sdk accounts objects metadata lookup mounts journal prior whole
    action present authority moving

-- §FS-host-boundary.publication: The public-source case constructs CURRENT authority
-- from the exact raw adapter, parent observations and shared native/child history before
-- extending custody. No independent authority, root or successful commit is an input.
theorem actual_commit_registered_custody_byte {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {semantics : NameSemanticsView} {dataObjects directories : ObjectId → Prop}
    (namespaceLaws : ByteNamespaceContract kernel semantics dataObjects)
    (namespaceFrames : ByteNamespaceFrameContract kernel semantics)
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
    (prior : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative)
    {trailing : List (ActorTick runtime)} (whole : all = processed ++ tick :: trailing)
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    (moving : request.op = .renameNew) :
    ∃ authority : PrimitiveCommitAuthority runtime initial all tick actor engine request observed hostUid semantics,
      ∃ root : CommitRootAt runtime authority.resources prior.current.source.custody.caps.family
          prior.current.source.custody.catalogue,
        ∃ updated : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
            foreignReferences (processed ++ [tick]) tick.after currentNative,
          updated.current.source.custody.catalogue = prior.current.source.custody.catalogue ∧
          ((tick.after.shared.entries = tick.before.shared.entries ∧
            updated.current.source.custody.caps = prior.current.source.custody.caps.retain tick.after.shared) ∨
          (Nonempty (CommitDelta authority.resources root.root.object) ∧
            updated.current.source.custody.caps = prior.current.source.custody.caps.published tick.after.shared root.root.object)) := by
  have selected : all[processed.length]? = some tick := by
    rw [whole, List.getElem?_append_right (by omega)]
    simp only [Nat.sub_self, List.getElem?_cons_zero]
  obtain ⟨authority⟩ := actual_primitive_commit_authority (backend := backend) descriptors aliases lifetimes references raw sdk accounts
    metadata nativeMetadata lookup probes journal authorityProfile lookupProfile recording selected present adapter moving
  obtain ⟨root, updated, catalogue, choice⟩ := commit_registered_custody_from_authority_byte namespaceLaws namespaceFrames
    descriptors aliases lifetimes references environment sdk accounts objects liveMetadata lookup mounts journal
    prior whole action present authority moving
  exact ⟨authority, root, updated, catalogue, choice⟩

-- §AR-host-boundary.interfaces: Keep the predecessor theorem's full type;
-- the raw cumulative consumer uses the current-byte-operand sibling.
theorem actual_commit_registered_custody {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {semantics : NameSemanticsView} {dataObjects directories : ObjectId → Prop}
    (namespaceLaws : ByteNamespaceContract kernel semantics dataObjects)
    (namespaceFrames : NamespaceContract kernel)
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
    (prior : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences processed tick.before currentNative)
    {trailing : List (ActorTick runtime)} (whole : all = processed ++ tick :: trailing)
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    (moving : request.op = .renameNew) :
    ∃ authority : PrimitiveCommitAuthority runtime initial all tick actor engine request observed hostUid semantics,
      ∃ root : CommitRootAt runtime authority.resources prior.current.source.custody.caps.family
          prior.current.source.custody.catalogue,
        ∃ updated : RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
            foreignReferences (processed ++ [tick]) tick.after currentNative,
          updated.current.source.custody.catalogue = prior.current.source.custody.catalogue ∧
          ((tick.after.shared.entries = tick.before.shared.entries ∧
            updated.current.source.custody.caps = prior.current.source.custody.caps.retain tick.after.shared) ∨
          (Nonempty (CommitDelta authority.resources root.root.object) ∧
            updated.current.source.custody.caps = prior.current.source.custody.caps.published tick.after.shared root.root.object)) := by
  exact actual_commit_registered_custody_byte (backend := backend) namespaceLaws (namespaceFrames.byteFrames semantics)
    descriptors aliases lifetimes references environment raw sdk accounts objects liveMetadata metadata nativeMetadata
    lookup probes mounts journal authorityProfile lookupProfile recording prior whole action present adapter moving

end LeanCage.Host.Kernel
