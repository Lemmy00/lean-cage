import FilesystemLoweredAliases
import FilesystemPrimitivePhases
import FilesystemCheckedParents
import FilesystemPublicationHandles
import FilesystemPathComponents
import FilesystemByteNamespaces
import FilesystemPublicParents

namespace LeanCage.Host.Kernel
open Filesystem

structure PrimitiveCommitResources {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    (initial : World) (ticks : List (ActorTick runtime)) (tick : ActorTick runtime)
    (actor : ActorId) (engine : EngineState) (request : Request) (observed : Option Reply) where
  adapter : PrimitiveAdapterAt runtime initial ticks tick actor engine request observed
  source : HostCommitCall adapter.occurrence.logicalBefore request none
  parent : ObservedParent kernel (fun ordinal request reply => SourceReturnAt runtime ticks actor ordinal Reply
    (.filesystem request) reply) engine.events.length (tick.before.project engine) source.source.commit.parent
  stage : Lowered.ObservedFresh kernel (fun ordinal request reply => SourceReturnAt runtime ticks actor ordinal Reply
    (.filesystem request) reply) engine.events.length (tick.before.project engine)
    source.source.commit.parent source.source.commit.stage parent.directory.handle
  parentBeforeGuard : parent.directory.sample.ordinal < adapter.occurrence.rawBefore.length
  selection : PrimitivePhaseAt runtime initial ticks tick actor engine
    (Directories.parent source.source.target true) (.ok source.source.commit.parent)
  parentAtSelection : selection.after.handles source.source.commit.parent.directory.fd = some parent.directory.handle
  selectionLimit : selection.rawBefore.length + selection.events.length ≤ engine.events.length

-- §FS-host-boundary.publication: The actual selected raw commit keeps its full source-selected
-- parent/stage/MAC/fill/marker prefix. Each raw FD and alias comes from those same actual chunks.
theorem primitive_commit_resources {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (aliases : DirectoryAliasContract kernel)
    {initial : World} {ticks : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial ticks tick actor engine request observed)
    (rename : request.op = .renameNew) :
    Nonempty (PrimitiveCommitResources runtime initial ticks tick actor engine request observed) := by
  have same := primitive_mutation_primary adapter.occurrence (by
    intro passive
    exact namespace_passive_no_rename request passive rename)
  have logical : Program.Prefix Entrypoint.run
      (adapter.occurrence.logicalBefore ++ [.lost (.filesystem request)]) := by
    simpa only [← same] using PrimitiveFilesystem.filesystem_occurrence_logical adapter.occurrence
  obtain ⟨source⟩ := entrypoint_commit_call (observed := none) logical rename
  obtain ⟨selection⟩ := primitive_filesystem_phase adapter source.source.commit.selected (commit_parent_trace source)
  let phase := selection.phase
  obtain ⟨parent⟩ := Lowered.parent_recorded descriptors _ phase.rawBefore.length source.source.target true phase.actual
  have chunks : PrimitiveFilesystem.Chunks
      (source.source.commit.creating.map Program.filesystemEvent ++ source.source.commit.preparing.map Program.filesystemEvent)
      selection.rawTail := by simpa only [List.map_append] using selection.chunks
  obtain ⟨creationRaw, preparationRaw, creationChunks, preparationChunks, rawTrace⟩ :=
    PrimitiveFilesystem.chunks_split _ _ chunks
  have history := phase.tail
  rw [selection.suffix, rawTrace, List.append_assoc] at history
  obtain ⟨createdAfter, creationHistory, afterCreation⟩ := actor_with_split creationRaw _ history
  obtain ⟨preparedAfter, preparationHistory, guarded⟩ :=
    actor_with_split preparationRaw (adapter.occurrence.inside.map Program.filesystemPrefixEvent) afterCreation
  obtain ⟨creationEvents, creationSource, creationTrace⟩ :=
    PrimitiveFilesystem.chunks_filesystem_returns source.source.commit.created creationChunks
  have creation : RecordedRun kernel (fun ordinal request reply => SourceReturnAt runtime ticks actor ordinal Reply
      (.filesystem request) reply) (phase.rawBefore.length + phase.events.length)
      (Directories.fresh source.source.commit.parent).lower phase.after creationEvents createdAfter
      (.ok source.source.commit.stage) :=
    ⟨creationSource, actor_recorded_filesystem (creationTrace ▸ creationHistory)⟩
  obtain ⟨stage⟩ := Lowered.fresh_recorded descriptors aliases _ _ source.source.commit.parent
    parent.directory.handle creation parent.directory.live
  obtain ⟨preparationEvents, preparationSource, preparationTrace⟩ :=
    PrimitiveFilesystem.chunks_filesystem_returns source.source.commit.prepared preparationChunks
  have preparation : RecordedRun kernel (fun ordinal request reply => SourceReturnAt runtime ticks actor ordinal Reply
      (.filesystem request) reply) (phase.rawBefore.length + phase.events.length + creationRaw.length)
      (Publication.prepare source.invocation.authenticated.bundle source.source.effective source.source.commit.display
        source.source.stdoutHash source.source.stderrHash source.source.commit.parent source.source.commit.stage).lower
      createdAfter preparationEvents preparedAfter (.ok source.source.commit.candidate) :=
    ⟨preparationSource, actor_recorded_filesystem (preparationTrace ▸ preparationHistory)⟩
  have retained : ∀ held handle, createdAfter.handles held = some handle →
      preparedAfter.handles held = some handle := by
    intro held handle live
    exact (Lowered.history_borrow held handle (Lowered.publication_prepare_borrow descriptors held handle _ _ _ _ _ _ _)
      preparation live).1
  have guards : (tick.before.project engine).handles = preparedAfter.handles :=
    actor_retaining_event_handles descriptors guarded
      (adapter_namespace_prefix_retaining adapter (.inr (.inr (.inr (.inl rename)))))
  have currentParent : (tick.before.project engine).handles source.source.commit.parent.directory.fd =
      some parent.directory.handle := by rw [guards]; exact retained _ _ stage.parentLive
  have currentContainer : (tick.before.project engine).handles source.source.commit.stage.container.fd =
      some stage.container.handle := by rw [guards]; exact retained _ _ stage.container.live
  have currentStage : (tick.before.project engine).handles source.source.commit.stage.directory.fd =
      some stage.directory.handle := by rw [guards]; exact retained _ _ stage.directory.live
  have phaseLength := congrArg List.length phase.trace
  simp only [List.length_append, List.length_map] at phaseLength
  have adapterLength := congrArg List.length adapter.occurrence.trace
  have suffixLength := congrArg List.length selection.suffix
  have phaseSuffixLength : phase.rawAfter.length = selection.phase.rawAfter.length := rfl
  simp only [List.length_append, List.length_map] at adapterLength suffixLength
  have limit : phase.rawBefore.length + phase.events.length ≤ engine.events.length := by omega
  have stageLimit : phase.rawBefore.length + phase.events.length + creationEvents.length ≤ engine.events.length := by
    have traceLength := congrArg List.length creationTrace
    have rawLength := congrArg List.length rawTrace
    simp only [List.length_append, List.length_map] at traceLength rawLength
    omega
  refine ⟨⟨adapter, source,
    ⟨parent.directory.advance currentParent limit, parent.identity, Nat.lt_of_lt_of_le parent.identityEarlier limit⟩,
    ⟨stage.directory.advance currentStage stageLimit, stage.container.advance currentContainer stageLimit,
      currentParent, stage.sameParent, stage.distinct⟩, ?_, phase, parent.directory.live, limit⟩⟩
  have earlier := parent.directory.earlier
  change parent.directory.sample.ordinal < adapter.occurrence.rawBefore.length
  omega

structure PrimitiveCommitAuthority {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    (initial : World) (ticks : List (ActorTick runtime)) (tick : ActorTick runtime)
    (actor : ActorId) (engine : EngineState) (request : Request) (observed : Option Reply)
    (hostUid : Nat) (semantics : NameSemanticsView) where
  resources : PrimitiveCommitResources runtime initial ticks tick actor engine request observed
  uid : resources.source.source.commit.parent.uid = hostUid
  information : Stat
  known : tick.before.shared.information resources.parent.directory.handle.object = some information
  trusted : Directories.trusted hostUid information = true
  names : (semantics.at tick.before.shared resources.parent.directory.handle.object).byteExact

-- §FS-host-boundary.publication: Actual caller/source resources, sampled UID/stat, continuous
-- OFD custody and the SAME raw guard establish current authority for both real rename parents.
theorem actual_primitive_commit_authority {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
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
    (backend : PrimitiveChildAuthorityProducer child ticks)
    (authorityProfile : NativeAuthorityProfile native ticks hostUid) (lookupProfile : NativeLookupProfile native ticks hostUid)
    {prior last : Processes} {callers next : NativeProcesses}
    (recording : NativeExternalJournal process child native hostUid prior callers ticks last next)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    (selected : ticks[position]? = some tick) (present : tick.before.actors actor = some engine)
    {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial ticks tick actor engine request observed)
    (rename : request.op = .renameNew) :
    Nonempty (PrimitiveCommitAuthority runtime initial ticks tick actor engine request observed hostUid semantics) := by
  obtain ⟨resources⟩ := primitive_commit_resources descriptors aliases adapter rename
  have uid := sampled_uid_is_host accounts resources.parent.identity
  cases uid
  have current : engine.references resources.source.source.commit.parent.directory.fd =
      some resources.parent.directory.handle := resources.parent.directory.live
  obtain ⟨interval, sameHandle, sameOrdinal⟩ := checked_parent_interval_owned descriptors lifetimes references raw sdk accounts
    journal backend recording selected present resources.parent.directory current resources.parent.directory.earlier
  have member : resources.source.source.commit.parent.directory.fd ∈ Lookup.parents request := by
    exact (congrArg (fun operation => resources.source.source.commit.parent.directory.fd ∈ Lookup.parents operation)
      resources.source.source.commit.operation).mpr (by simp [Lookup.parents])
  have earlier : interval.sample.ordinal < resources.adapter.occurrence.rawBefore.length := by
    rw [sameOrdinal]
    exact resources.parentBeforeGuard
  obtain ⟨information, known, trusted, names⟩ := checked_parent_comparison lifetimes metadata nativeMetadata lookup
    probes journal authorityProfile lookupProfile interval resources.adapter (.inr (.inr (.inr (.inl rename))))
    resources.source.source.commit.parent.directory.fd member interval.parent interval.reference rfl earlier
  exact ⟨⟨resources, rfl, information, by simpa only [sameHandle] using known, trusted,
    by simpa only [sameHandle] using names⟩⟩

-- §FS-host-boundary.publication: The commit target's public role comes from the SAME actual
-- caller selection and all real raw lookups, including interleaved publication of older trees.
theorem PrimitiveCommitAuthority.public_target {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
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
    (authority : PrimitiveCommitAuthority runtime initial ticks tick actor engine request observed hostUid semantics) :
    family authority.resources.parent.directory.handle.object = none := by
  obtain ⟨handle, live, publicObject⟩ := Lowered.parent_history_public descriptors aliases lifetimes lookup cwdLookup
    journal selected present shape count prefixLabels authority.resources.selection.rawBefore.length
    authority.resources.source.source.target true authority.resources.selection.actual authority.resources.selectionLimit
  have same : handle = authority.resources.parent.directory.handle :=
    Option.some.inj (live.symm.trans authority.resources.parentAtSelection)
  simpa only [same] using publicObject

-- §FS-host-boundary.publication: Every one-operation namespace premise is supplied by the
-- actual source-selected components, real raw handles and derived CURRENT parent comparison.
theorem PrimitiveCommitAuthority.namespace_delta {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {hostUid : Nat} {semantics : NameSemanticsView} {dataObjects : ObjectId → Prop}
    (laws : ByteNamespaceContract kernel semantics dataObjects)
    {initial : World} {ticks : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (authority : PrimitiveCommitAuthority runtime initial ticks tick actor engine request observed hostUid semantics)
    (actual : kernel.step (tick.before.project engine) request observed tick.after.shared)
    (rename : request.op = .renameNew) : DataChange dataObjects request (tick.before.project engine) tick.after.shared := by
  let source := authority.resources.source.source.commit
  have target := selected_parent_component authority.resources.source.source.target true source.selected
  have stage := selected_fresh_component source.parent source.created
  have components : ComponentRequest request :=
    (congrArg ComponentRequest source.operation).mpr ⟨stage.1, target.1⟩
  have operands : DirectoryOperands (tick.before.project engine) request :=
    (congrArg (DirectoryOperands (tick.before.project engine)) source.operation).mpr
      ⟨⟨authority.resources.stage.container.handle, authority.resources.stage.container.live⟩,
        ⟨authority.resources.parent.directory.handle, authority.resources.stage.parentLive⟩⟩
  apply laws.mutation _ _ _ _ actual (.inr (.inr (.inl rename))) components operands
  intro fd member handle live
  have parents : Lookup.parents request = [source.stage.container.fd, source.parent.directory.fd] :=
    (congrArg Lookup.parents source.operation).trans rfl
  rw [parents] at member
  rcases List.mem_cons.mp member with rfl | later
  · have same := Option.some.inj (live.symm.trans authority.resources.stage.container.live)
    subst handle
    simpa only [NameSemanticsView.at, Population.project, authority.resources.stage.sameParent] using authority.names
  · have sameFd := List.mem_singleton.mp later
    subst fd
    have same := Option.some.inj (live.symm.trans authority.resources.stage.parentLive)
    subst handle
    exact authority.names

end LeanCage.Host.Kernel
