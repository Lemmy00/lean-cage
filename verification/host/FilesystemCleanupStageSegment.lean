import FilesystemCleanupBorrowing
import FilesystemPendingBorrowing
import FilesystemPrimitivePrefixPhases

namespace LeanCage.Host.Kernel
open Filesystem

private theorem last_pending {α : Type} {program : Filesystem.Program α}
    {before : List (Request × Option Reply)} {request : Request} {observed : Option Reply}
    (source : Prefix program (before ++ [(request, observed)])) :
    Prefix program (before ++ [(request, none)]) := by
  generalize trace : before ++ [(request, observed)] = events at source
  induction source generalizing before with
  | empty =>
    have length := congrArg List.length trace
    simp only [List.length_append, List.length_singleton, List.length_nil] at length
    omega
  | lost actual next =>
    cases before with
    | nil => cases trace; exact .lost _ _
    | cons head tail =>
      have length := congrArg List.length trace
      simp only [List.length_cons, List.length_append, List.length_nil] at length
      omega
  | returned actual next reply tail rest ih =>
    cases before with
    | nil => cases trace; exact .lost _ _
    | cons head earlier =>
      have same := List.cons.inj trace
      exact same.1 ▸ Prefix.returned actual next reply _ (ih same.2)

structure CleanupStageSegment {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {before : List Program.Event} {request : Request}
    {call : PublicationCleanup.Host before request} {limit : Nat} {current : World}
    (source : CleanupStageContinuation runtime initial all call limit current) where
  beforeRaw : List Program.Event
  events : List (Request × Reply)
  cleanupRaw : List Program.Event
  chunks : PrimitiveFilesystem.Chunks (call.source.attempt.inside.map Program.filesystemPrefixEvent) cleanupRaw
  trace : events.map Program.filesystemEvent = cleanupRaw ++ source.earlier.guards
  world : World
  history : RecordedHistory kernel (fun ordinal query reply =>
    SourceReturnAt runtime all source.earlier.source.inputActor ordinal Reply (.filesystem query) reply)
    beforeRaw.length world events current
  actorHistory : ActorHistoryWith runtime source.earlier.source.inputActor
    (SourceReturnAt runtime all source.earlier.source.inputActor) beforeRaw.length world
    (cleanupRaw ++ source.earlier.guards) current
  active : Prefix (Publication.cleanup call.source.attempt.context.parent call.source.attempt.context.stage
    call.source.effective).lower (Publication.completed events ++ [(request, none)])
  directory : world.handles call.source.attempt.context.stage.directory.fd = some source.earlier.source.opening.handle
  container : world.handles call.source.attempt.context.stage.container.fd = some source.root.use.parent
  distinct : call.source.attempt.context.stage.directory.fd ≠ call.source.attempt.context.stage.container.fd
  observation : ObservedDirectory kernel (fun ordinal query reply =>
    SourceReturnAt runtime all source.earlier.source.inputActor ordinal Reply (.filesystem query) reply)
    beforeRaw.length world call.source.attempt.context.parent.uid call.source.attempt.context.stage.directory
  sameObserved : observation.handle = source.earlier.source.opening.handle
  preparingRaw : List Program.Event
  preparingChunks : PrimitiveFilesystem.Chunks (call.source.attempt.preparing.map Program.filesystemEvent) preparingRaw
  followingTrace : source.earlier.remaining = source.opening.after.map Program.filesystemEvent ++ preparingRaw ++ cleanupRaw
  beforeTrace : beforeRaw = source.earlier.source.input.events ++
    .returned (.filesystem source.opening.request) source.opening.reply ::
      (source.earlier.post.map Program.filesystemEvent ++ source.opening.after.map Program.filesystemEvent ++ preparingRaw)

-- §FS-host-boundary.publication: The SAME actual failed preparation feeds
-- cleanup's pending syscall, retaining every raw probe and its real source
-- ordinal. No successful preparation, removal or future ACK is assumed.
theorem actual_cleanup_stage_segment {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel)
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    {call : PublicationCleanup.Host adapter.occurrence.logicalBefore request} {limit : Nat}
    (source : CleanupStageContinuation runtime initial all call limit (tick.before.project engine))
    (guards : source.earlier.guards = adapter.occurrence.inside.map Program.filesystemPrefixEvent)
    (unlink : request.op = .unlinkAt) : Nonempty (CleanupStageSegment source) := by
  obtain ⟨point⟩ := source.allocation descriptors
  obtain ⟨preparingRaw, cleanupRaw, preparingChunks, cleanupChunks, rawTrace⟩ :=
    PrimitiveFilesystem.chunks_split (call.source.attempt.preparing.map Program.filesystemEvent)
      (call.source.attempt.inside.map Program.filesystemPrefixEvent) point.chunks
  have history : ActorHistoryWith runtime source.earlier.source.inputActor
      (SourceReturnAt runtime all source.earlier.source.inputActor)
      (source.earlier.source.input.events.length + 1 +
        (source.earlier.post.map Program.filesystemEvent).length + point.inspectionRaw.length)
      point.world (preparingRaw ++ (cleanupRaw ++ source.earlier.guards)) (tick.before.project engine) := by
    have actual := Eq.mp (congrArg (fun raw => ActorHistoryWith runtime source.earlier.source.inputActor
      (SourceReturnAt runtime all source.earlier.source.inputActor)
      (source.earlier.source.input.events.length + 1 +
        (source.earlier.post.map Program.filesystemEvent).length + point.inspectionRaw.length)
      point.world (raw ++ source.earlier.guards) (tick.before.project engine)) rawTrace) point.history
    simpa only [List.append_assoc] using actual
  obtain ⟨world, preparationHistory, cleanupHistory⟩ := actor_with_split preparingRaw _ history
  obtain ⟨preparing, prepared, preparationTrace⟩ :=
    PrimitiveFilesystem.chunks_filesystem_returns call.source.attempt.prepared preparingChunks
  have preparation : RecordedRun kernel (fun ordinal query reply =>
      SourceReturnAt runtime all source.earlier.source.inputActor ordinal Reply (.filesystem query) reply)
      (source.earlier.source.input.events.length + 1 +
        (source.earlier.post.map Program.filesystemEvent).length + point.inspectionRaw.length)
      (Publication.prepare call.invocation.authenticated.bundle call.source.effective call.source.attempt.context.display
        call.source.stdoutHash call.source.stderrHash call.source.attempt.context.parent call.source.attempt.context.stage).lower
      point.world preparing world (.error call.source.attempt.error) :=
    ⟨prepared, actor_recorded_filesystem (preparationTrace ▸ preparationHistory)⟩
  have directory := (Lowered.history_borrow _ _
    (Lowered.publication_prepare_borrow descriptors _ _ _ _ _ _ _ _ _) preparation point.directory).1
  have container := (Lowered.history_borrow _ _
    (Lowered.publication_prepare_borrow descriptors _ _ _ _ _ _ _ _ _) preparation point.container).1
  have primary : request = adapter.occurrence.primary := primitive_mutation_primary adapter.occurrence (by
    intro passive
    simp only [NamespacePassive, unlink] at passive)
  have rawAdapter : Program.Prefix (PrimitiveFilesystem.lowerEffect (.filesystem request))
      (adapter.occurrence.inside.map Program.filesystemPrefixEvent ++ [.lost (.filesystem request)]) := by
    have active := Program.lift_filesystem_prefix (last_pending adapter.occurrence.adapter)
    rw [← primary] at active
    simpa only [PrimitiveFilesystem.lowerEffect, List.map_append, List.map_singleton,
      Program.filesystemPrefixEvent] using active
  have cleanupSource := Program.lift_filesystem_prefix call.source.attempt.active
  simp only [List.map_append, List.map_singleton, Program.filesystemPrefixEvent] at cleanupSource
  have lowered := PrimitiveFilesystem.pending_chunks_prefix (.filesystem request) cleanupSource cleanupChunks rawAdapter
  rw [PrimitiveFilesystem.lower_lift_filesystem] at lowered
  have lowered : Program.Prefix (Program.liftFilesystem
      (Publication.cleanup call.source.attempt.context.parent call.source.attempt.context.stage call.source.effective).lower)
      ((cleanupRaw ++ source.earlier.guards) ++ [Program.filesystemPrefixEvent (request, none)]) := by
    simpa only [guards, List.append_assoc, Program.filesystemPrefixEvent] using lowered
  obtain ⟨earlier, active, earlierTrace⟩ := selected_filesystem_source lowered
  obtain ⟨events, completedTrace, recorded⟩ := actor_raw_filesystem (earlierTrace ▸ cleanupHistory)
  have exactTrace : events.map Program.filesystemEvent = cleanupRaw ++ source.earlier.guards := by
    rw [earlierTrace, completedTrace, List.map_map]
    rfl
  let beforeRaw := source.earlier.source.input.events ++
    .returned (.filesystem source.opening.request) source.opening.reply ::
      (source.earlier.post.map Program.filesystemEvent ++ point.inspectionRaw ++ preparingRaw)
  have beforeCount : beforeRaw.length = source.earlier.source.input.events.length + 1 +
      (source.earlier.post.map Program.filesystemEvent).length + point.inspectionRaw.length + preparingRaw.length := by
    simp only [beforeRaw, List.length_append, List.length_cons]
    omega
  have recorded : RecordedHistory kernel (fun ordinal query reply =>
      SourceReturnAt runtime all source.earlier.source.inputActor ordinal Reply (.filesystem query) reply)
      beforeRaw.length world events (tick.before.project engine) := by
    rw [beforeCount]
    exact actor_recorded_filesystem (exactTrace.symm ▸ cleanupHistory)
  refine ⟨{
    beforeRaw
    events
    cleanupRaw
    chunks := cleanupChunks
    trace := exactTrace
    world
    history := recorded
    actorHistory := by rw [beforeCount]; exact cleanupHistory
    active := ?_
    directory
    container
    distinct := point.distinct
    observation := point.observation.advance (by rw [point.sameObserved]; exact directory) ?_
    sameObserved := point.sameObserved
    preparingRaw
    preparingChunks
    followingTrace := by rw [point.trace, rawTrace, point.inspectionExact]; simp only [List.append_assoc]
    beforeTrace := by simp only [beforeRaw, point.inspectionExact] }⟩
  · simpa only [completedTrace, Publication.completed] using active
  · rw [beforeCount]
    omega

-- §FS-host-boundary.ownership: All removals retain the original container;
-- inner removals also precede the stage close. Integer FD reuse after that
-- close cannot become a new authority for an inner cleanup operation.
theorem CleanupStageSegment.current_container {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel)
    {initial : World} {all : List (ActorTick runtime)} {before : List Program.Event} {request : Request}
    {call : PublicationCleanup.Host before request} {limit : Nat} {current : World}
    {source : CleanupStageContinuation runtime initial all call limit current}
    (segment : CleanupStageSegment source) (unlink : request.op = .unlinkAt) :
    current.handles call.source.attempt.context.stage.container.fd = some source.root.use.parent :=
  borrowed_pending_reference (Lowered.cleanup_container_uses descriptors _ _ _ _ (Ne.symm segment.distinct))
    segment.active segment.history segment.container unlink

theorem CleanupStageSegment.current_directory {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel)
    {initial : World} {all : List (ActorTick runtime)} {before : List Program.Event} {request : Request}
    {call : PublicationCleanup.Host before request} {limit : Nat} {current : World}
    {source : CleanupStageContinuation runtime initial all call limit current}
    (segment : CleanupStageSegment source) (unlink : request.op = .unlinkAt)
    (inner : request.first ≠ call.source.attempt.context.stage.container.fd) :
    current.handles call.source.attempt.context.stage.directory.fd = some source.earlier.source.opening.handle :=
  borrowed_pending_reference (Lowered.cleanup_stage_uses descriptors _ _ _ _)
    segment.active segment.history segment.directory ⟨unlink, inner⟩

theorem CleanupStageSegment.event_trace {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {before : List Program.Event} {request : Request}
    {call : PublicationCleanup.Host before request} {limit : Nat} {current : World}
    {source : CleanupStageContinuation runtime initial all call limit current}
    (segment : CleanupStageSegment source) {events : List Program.Event}
    (trace : events = source.earlier.source.input.events ++
      .returned (.filesystem source.opening.request) source.opening.reply ::
        (source.earlier.post.map Program.filesystemEvent ++ source.earlier.remaining ++ source.earlier.guards)) :
    events = segment.beforeRaw ++ segment.events.map Program.filesystemEvent := by
  rw [trace, segment.beforeTrace, segment.trace, segment.followingTrace]
  simp only [List.append_assoc, List.cons_append]

end LeanCage.Host.Kernel
