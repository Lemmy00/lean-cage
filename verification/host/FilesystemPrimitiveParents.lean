import FilesystemPrimitiveObservations
import FilesystemPrimitiveFrames
import FilesystemMkdirOrigins
import FilesystemPrimitivePhases
import FilesystemLoweredDirectories

namespace LeanCage.Host.Kernel
open Filesystem

structure PrimitiveMkdirSite {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    (initial : World) (ticks : List (ActorTick runtime)) (tick : ActorTick runtime)
    (actor : ActorId) (engine : EngineState) (request : Request) (observed : Option Reply) where
  adapter : PrimitiveAdapterAt runtime initial ticks tick actor engine request observed
  same : request = adapter.occurrence.primary
  site : HostMkdirSite adapter.occurrence.logicalBefore request none

-- §FS-host-boundary.ownership: The actual raw mkdir has a run/validator or publication source,
-- even when its acknowledgement is an error or is lost.
theorem actual_primitive_mkdir_site {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (environment : InterferenceContract kernel)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply} (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) (mkdir : request.op = .mkdirAt) :
    Nonempty (PrimitiveMkdirSite runtime initial ticks tick actor engine request observed) := by
  obtain ⟨adapter⟩ := actual_primitive_adapter descriptors lifetimes references environment
    journal selected action present
  have same := PrimitiveFilesystem.filesystem_occurrence_primary adapter.occurrence
    (by intro wrong; rw [mkdir] at wrong; cases wrong)
    (by intro wrong; rw [mkdir] at wrong; cases wrong)
    (by intro wrong; rw [mkdir] at wrong; cases wrong)
  have logical : Program.Prefix Entrypoint.run
      (adapter.occurrence.logicalBefore ++ [.lost (.filesystem request)]) := by
    simpa only [← same] using PrimitiveFilesystem.filesystem_occurrence_logical adapter.occurrence
  obtain ⟨site⟩ := entrypoint_mkdir_site (observed := none) logical mkdir
  exact ⟨⟨adapter, same, site⟩⟩

structure PrimitiveRunParent {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    (initial : World) (ticks : List (ActorTick runtime)) (tick : ActorTick runtime)
    (actor : ActorId) (engine : EngineState) (request : Request) where
  container : Directories.Opened
  uid : Nat
  identityReply : Reply
  statReply : Reply
  identity : PrimitiveObservationAt runtime initial ticks tick actor engine (.filesystem { op := .euid }) identityReply
  inspected : PrimitiveObservationAt runtime initial ticks tick actor engine
    (.filesystem { op := .stat, first := container.fd }) statReply
  successful : nativeError identityReply = false
  empty : identityReply.2 = .empty
  uidValue : uid = identityReply.1.toNat
  parsed : parseStat statReply = some container.information
  trusted : Directories.trusted uid container.information = true
  parentArgument : request.first = container.fd
  privateMode : request.second = 448
  component : Directories.component request.left = true
  reserved : PrivateNames.reservedBytes request.left = true
  retainedAfterStat : ∀ event ∈ inspected.rawAfter, RetainingEvent event
  opened : PrimitivePhaseAt runtime initial ticks tick actor engine (Directories.openAt uid cwd "/tmp".toUTF8) (.ok container)
  retainedAfterOpen : ∀ event ∈ opened.rawAfter, RetainingEvent event
  observed : Option Reply
  adapter : PrimitiveAdapterAt runtime initial ticks tick actor engine request observed
  invocation : RunCreationPrefix adapter.occurrence.logicalBefore request none
  statBeforeGuard : inspected.rawBefore.length < adapter.occurrence.rawBefore.length
  mkdir : request.op = .mkdirAt

-- §FS-host-boundary.ownership: The same run mkdir's parent/UID/stat arguments and bytes come
-- from its actual temporaryParent helper and completed raw chunks, not a physical helper frame.
theorem primitive_run_parent_observations {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {ticks : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial ticks tick actor engine request observed)
    (invocation : RunCreationPrefix adapter.occurrence.logicalBefore request none)
    (mkdir : request.op = .mkdirAt) :
    Nonempty (PrimitiveRunParent runtime initial ticks tick actor engine request) := by
  obtain ⟨source⟩ := actual_run_child_call invocation.active mkdir
  obtain ⟨path, identityReply, opening, selectingTrace, successful, empty, uidValue, bounded, opened⟩ :=
    RunDirectory.temporaryParent_source source.selected
  obtain ⟨openReply, statReply, openingTrace, recognized, parsed, trusted⟩ :=
    Retrieval.directoryOpening_source _ _ _ (directory_observation_returns source.uid cwd "/tmp".toUTF8 opened)
  have trace : adapter.occurrence.logicalBefore = invocation.context ++
      .returned (.filesystem { op := .euid }) identityReply ::
      .returned (.filesystem { op := .openAt, first := cwd, second := directoryFlags, left := "/tmp".toUTF8 }) openReply ::
      .returned (.filesystem { op := .stat, first := source.container.fd }) statReply ::
      source.child.randomEvents.map Program.filesystemEvent := by
    calc
      adapter.occurrence.logicalBefore = invocation.context ++ invocation.inside.map Program.filesystemPrefixEvent :=
        invocation.trace
      _ = _ := by
        conv => lhs; rw [source.trace, source.child.trace, selectingTrace, openingTrace]
        simp only [List.map_append, completed_filesystem_events, List.map_cons, List.map_nil,
          Program.filesystemEvent, List.cons_append, List.nil_append]
  obtain ⟨identity⟩ := primitive_observation adapter trace PrimitiveFilesystem.euid_identity
  have statTrace : adapter.occurrence.logicalBefore = (invocation.context ++
      [.returned (.filesystem { op := .euid }) identityReply,
       .returned (.filesystem { op := .openAt, first := cwd, second := directoryFlags, left := "/tmp".toUTF8 }) openReply]) ++
      .returned (.filesystem { op := .stat, first := source.container.fd }) statReply ::
      source.child.randomEvents.map Program.filesystemEvent := by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using trace
  obtain ⟨statChunked⟩ := primitive_observation_chunked adapter statTrace (PrimitiveFilesystem.stat_identity _)
  let inspected := statChunked.observation
  have remaining : statChunked.rawTail = source.child.randomEvents.map Program.filesystemEvent :=
    PrimitiveFilesystem.chunks_identity statChunked.chunks (random_events_identity source.child.randomness)
  have retains : ∀ event ∈ inspected.rawAfter, RetainingEvent event := by
    intro event member
    have suffix : inspected.rawAfter = source.child.randomEvents.map Program.filesystemEvent ++
        adapter.occurrence.inside.map Program.filesystemPrefixEvent := by
      simpa only [remaining] using statChunked.suffix
    rw [suffix] at member
    rcases List.mem_append.mp member with random | checks
    · exact random_events_retaining source.child.randomness event random
    · exact adapter_namespace_prefix_retaining adapter (.inr (.inl mkdir)) event checks
  have openingSource := directory_observation_returns source.uid cwd "/tmp".toUTF8 opened
  have phaseTrace : adapter.occurrence.logicalBefore =
      (invocation.context ++ [.returned (.filesystem {op := .euid}) identityReply]) ++
      opening.map Program.filesystemEvent ++ source.child.randomEvents.map Program.filesystemEvent := by
    simpa only [openingTrace, List.map_cons, List.map_nil, Program.filesystemEvent, List.singleton_append,
      List.cons_append, List.nil_append, List.append_assoc] using trace
  obtain ⟨openingChunked⟩ := primitive_filesystem_phase adapter openingSource phaseTrace
  have openingTail : openingChunked.rawTail = source.child.randomEvents.map Program.filesystemEvent :=
    PrimitiveFilesystem.chunks_identity openingChunked.chunks (random_events_identity source.child.randomness)
  have openingRetains : ∀ event ∈ openingChunked.phase.rawAfter, RetainingEvent event := by
    intro event member
    have suffix : openingChunked.phase.rawAfter = source.child.randomEvents.map Program.filesystemEvent ++
        adapter.occurrence.inside.map Program.filesystemPrefixEvent := by
      simpa only [openingTail] using openingChunked.suffix
    rw [suffix] at member
    rcases List.mem_append.mp member with random | checks
    · exact random_events_retaining source.child.randomness event random
    · exact adapter_namespace_prefix_retaining adapter (.inr (.inl mkdir)) event checks
  refine ⟨⟨source.container, source.uid, identityReply, statReply, identity, inspected,
    successful, empty, uidValue, parsed, trusted, ?_, ?_, ?_, ?_, retains,
    openingChunked.phase, openingRetains, observed, adapter, invocation, statChunked.before_guard, mkdir⟩⟩
  · exact congrArg Request.first source.child.operation
  · exact congrArg Request.second source.child.operation
  · simpa only [source.child.operation] using source.child.component
  · rw [source.child.operation]
    exact private_prefix_reserved _

theorem primitive_run_parent_uid {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {ticks : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {hostUid : Nat}
    (accounts : AccountContract kernel hostUid)
    (source : PrimitiveRunParent runtime initial ticks tick actor engine request) : source.uid = hostUid :=
  source.uidValue.trans (primitive_uid_is_host accounts source.identity source.successful source.empty)

-- §FS-host-boundary.ownership: Successful actual guarded open/stat creates the parent lease;
-- only actual random/probe calls follow it before the selected mkdir, including failure/loss.
theorem primitive_run_parent_reference {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {ticks : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request}
    (descriptors : DescriptorContract kernel)
    (source : PrimitiveRunParent runtime initial ticks tick actor engine request) :
    ∃ handle, engine.references request.first = some handle ∧ handle.rawOwned = true := by
  obtain ⟨observed⟩ := Lowered.directory_open_recorded descriptors _ source.opened.rawBefore.length
    source.uid cwd "/tmp".toUTF8 source.opened.actual
  have frames := actor_retaining_event_handles descriptors source.opened.tail source.retainedAfterOpen
  have current : (tick.before.project engine).handles source.container.fd = some observed.handle := by
    rw [frames]
    exact observed.live
  exact ⟨observed.handle, by simpa only [source.parentArgument, Population.project] using current, observed.raw⟩

-- §FS-host-boundary.ownership: The retained temporary parent also carries its real absolute
-- open occurrence, for initial-anchor/path resolution and later same-birth registry use.
theorem primitive_run_parent_open {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {ticks : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request}
    (descriptors : DescriptorContract kernel)
    (source : PrimitiveRunParent runtime initial ticks tick actor engine request) :
    ∃ opening : Lowered.RecordedOpen kernel (fun index request reply =>
        SourceReturnAt runtime ticks actor index Reply (.filesystem request) reply)
        {op := .openAt, first := cwd, second := directoryFlags, left := "/tmp".toUTF8} source.container.fd,
      engine.references request.first = some opening.handle := by
  obtain ⟨opening, observed, same⟩ := Lowered.directory_open_recorded_owned descriptors _ source.opened.rawBefore.length
    source.uid cwd "/tmp".toUTF8 source.opened.actual
  have frame := actor_retaining_event_handles descriptors source.opened.tail source.retainedAfterOpen
  have current : (tick.before.project engine).handles source.container.fd = some opening.handle := by
    rw [frame, ← same]
    exact observed.live
  exact ⟨opening, by simpa only [source.parentArgument, Population.project] using current⟩

-- §FS-host-boundary.ownership: The actual current mkdir reference is the one inspected earlier.
-- Its metadata is sampled at that real stat; later authority uses per-global-operation laws.
theorem primitive_run_parent_observed {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {ticks : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {hostUid : Nat}
    (descriptors : DescriptorContract kernel) (accounts : AccountContract kernel hostUid)
    (source : PrimitiveRunParent runtime initial ticks tick actor engine request)
    {parent : Handle} (live : engine.references request.first = some parent) :
    source.inspected.before.handles source.container.fd = some parent ∧
      source.inspected.before.information parent.object = some source.container.information ∧
      Directories.trusted hostUid source.container.information = true := by
  have afterFrames := actor_retaining_event_handles descriptors source.inspected.tail source.retainedAfterStat
  have statFrames := descriptors.retained _ _ _ _ source.inspected.actual (by simp [RetainsDescriptors])
  have current : (tick.before.project engine).handles source.container.fd = some parent := by
    simpa only [source.parentArgument, Population.project] using live
  have atStat : source.inspected.before.handles source.container.fd = some parent := by
    rw [← statFrames, ← afterFrames]
    exact current
  refine ⟨atStat, primitive_stat_information descriptors source.inspected atStat source.parsed, ?_⟩
  have sameUid := primitive_run_parent_uid accounts source
  simpa only [sameUid] using source.trusted

end LeanCage.Host.Kernel
