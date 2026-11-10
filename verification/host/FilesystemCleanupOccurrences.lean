import FilesystemRunCleanupReference
import FilesystemCleanupUses
import FilesystemPrimitivePrefixPhases

namespace LeanCage.Host.Kernel
open Filesystem

private theorem prefix_map_injective {first last : List (Request × Option Reply)}
    (same : first.map Program.filesystemPrefixEvent = last.map Program.filesystemPrefixEvent) : first = last := by
  induction first generalizing last with
  | nil => cases last <;> cases same; rfl
  | cons head tail ih =>
    cases last with
    | nil => cases same
    | cons following rest =>
      have fields := List.cons.inj same
      have decoded := congrArg PrimitiveFilesystem.filesystemEvent? fields.1
      have pair : head = following := by
        simpa only [PrimitiveFilesystem.filesystem_event_decode, Option.some.injEq] using decoded
      rw [pair, ih fields.2]

private theorem lift_prefix_exact {α : Type} {program : Filesystem.Program α}
    {events : List (Request × Option Reply)}
    (source : Program.Prefix (Program.liftFilesystem program) (events.map Program.filesystemPrefixEvent)) :
    Prefix program events := by
  obtain ⟨actual, active, trace⟩ := Program.lift_filesystem_prefix_source _ source
  have same := prefix_map_injective trace
  exact same.symm ▸ active

structure CleanupOccurrenceSegment {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {actor : ActorId} {events outside : List Program.Event}
    {created : List (Request × Reply)} {run : RunDirectory.Owned} {work : List Program.Event}
    {inside : List (Request × Option Reply)} {request : Request} {guardOrdinal limit : Nat} {current : World}
    (source : RunCleanupParent runtime initial all actor events outside created run work inside request guardOrdinal limit current) where
  beforeRaw : List Program.Event
  cleanupEvents : List (Request × Reply)
  chunks : PrimitiveFilesystem.Chunks (inside.map Program.filesystemPrefixEvent)
    (cleanupEvents.map Program.filesystemEvent)
  trace : events = beforeRaw ++ cleanupEvents.map Program.filesystemEvent ++ source.allocation.earlier.guards
  beforeCleanup : World
  afterCleanup : World
  history : RecordedHistory kernel (fun ordinal query reply =>
    SourceReturnAt runtime all source.allocation.earlier.source.inputActor ordinal Reply (.filesystem query) reply)
    beforeRaw.length beforeCleanup cleanupEvents afterCleanup
  active : Prefix (RunDirectory.cleanup run).lower (Publication.completed cleanupEvents)
  directory : beforeCleanup.handles run.directory.fd = some source.allocation.earlier.source.opening.handle
  workRaw : List Program.Event
  workChunks : PrimitiveFilesystem.Chunks work workRaw
  beforeTrace : beforeRaw = source.allocation.earlier.source.input.events ++
    .returned (.filesystem source.allocation.opening.request) source.allocation.opening.reply ::
      (source.allocation.earlier.post.map Program.filesystemEvent ++ source.point.createdAfter ++ workRaw)

-- §FS-host-boundary.ownership: Split the actual work and finite cleanup
-- prefix on ONE lowering/history witness. The captured directory is valid
-- at cleanup entry even when its later close has already occurred.
theorem actual_cleanup_occurrence_segment {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {actor : ActorId} {events outside : List Program.Event}
    {created : List (Request × Reply)} {run : RunDirectory.Owned} {work : List Program.Event}
    {inside : List (Request × Option Reply)} {request : Request} {guardOrdinal limit : Nat} {current : World}
    (source : RunCleanupParent runtime initial all actor events outside created run work inside request guardOrdinal limit current) :
    Nonempty (CleanupOccurrenceSegment source) := by
  obtain ⟨workRaw, cleanupRaw, workChunks, cleanupChunks, rawTrace⟩ :=
    PrimitiveFilesystem.chunks_split work (inside.map Program.filesystemPrefixEvent) source.point.chunks
  have originalCleanupChunks := cleanupChunks
  have history : ActorHistoryWith runtime source.allocation.earlier.source.inputActor
      (SourceReturnAt runtime all source.allocation.earlier.source.inputActor)
      (source.allocation.earlier.source.input.events.length + 1 +
        (source.allocation.earlier.post.map Program.filesystemEvent).length + source.point.createdAfter.length)
      source.point.world (workRaw ++ (cleanupRaw ++ source.allocation.earlier.guards)) current := by
    have actual := Eq.mp (congrArg (fun raw => ActorHistoryWith runtime source.allocation.earlier.source.inputActor
      (SourceReturnAt runtime all source.allocation.earlier.source.inputActor)
      (source.allocation.earlier.source.input.events.length + 1 +
        (source.allocation.earlier.post.map Program.filesystemEvent).length + source.point.createdAfter.length)
      source.point.world (raw ++ source.allocation.earlier.guards) current) rawTrace) source.point.history
    simpa only [List.append_assoc] using actual
  obtain ⟨beforeCleanup, workHistory, remaining⟩ := actor_with_split workRaw _ history
  obtain ⟨afterCleanup, cleanupHistory, guards⟩ := actor_with_split cleanupRaw _ remaining
  have directory := (actor_borrow_recorded_returns
    (source.workBorrows _ _ _ source.point.directoryRaw) workHistory
    (PrimitiveFilesystem.chunks_returns source.worked workChunks) source.point.directory).1
  obtain ⟨frontier⟩ := cleanup_frontier source.cleanupSource
  have cleanupChunks : PrimitiveFilesystem.Chunks (frontier.replies.map Program.filesystemEvent) cleanupRaw :=
    Eq.mp (congrArg (fun logical => PrimitiveFilesystem.Chunks logical cleanupRaw)
      ((congrArg (List.map Program.filesystemPrefixEvent) frontier.trace).trans (completed_filesystem_events _))) cleanupChunks
  obtain ⟨cleanupEvents, cleanupTrace⟩ := PrimitiveFilesystem.chunks_filesystem_raw frontier.replies cleanupChunks
  have logicalSource : Program.Prefix (Program.liftFilesystem (RunDirectory.cleanup run))
      (frontier.replies.map Program.filesystemEvent ++ [.lost (.filesystem request)]) := by
    have actual := Program.lift_filesystem_prefix source.cleanupSource
    exact Eq.mp (congrArg (fun events => Program.Prefix (Program.liftFilesystem (RunDirectory.cleanup run)) events)
      (by simp only [frontier.trace, List.map_append, List.map_singleton, completed_filesystem_events,
        Program.filesystemPrefixEvent])) actual
  obtain ⟨next, reached⟩ := PrimitiveFilesystem.pending_residual (.filesystem request) logicalSource
  have actualPrefix := PrimitiveFilesystem.reached_prefix
    (PrimitiveFilesystem.reached_of_chunks reached cleanupChunks) (Program.Prefix.empty _)
  have actualPrefix : Program.Prefix (Program.liftFilesystem (RunDirectory.cleanup run).lower)
      ((Publication.completed cleanupEvents).map Program.filesystemPrefixEvent) := by
    simpa only [List.append_nil, PrimitiveFilesystem.lower_lift_filesystem, cleanupTrace,
      completed_filesystem_events] using actualPrefix
  let beforeRaw := source.allocation.earlier.source.input.events ++
    .returned (.filesystem source.allocation.opening.request) source.allocation.opening.reply ::
      (source.allocation.earlier.post.map Program.filesystemEvent ++ source.point.createdAfter ++ workRaw)
  have beforeCount : beforeRaw.length = source.allocation.earlier.source.input.events.length + 1 +
      (source.allocation.earlier.post.map Program.filesystemEvent).length + source.point.createdAfter.length + workRaw.length := by
    simp only [beforeRaw, List.length_append, List.length_cons]
    omega
  have cleanupHistory : RecordedHistory kernel (fun ordinal query reply =>
      SourceReturnAt runtime all source.allocation.earlier.source.inputActor ordinal Reply (.filesystem query) reply)
      beforeRaw.length beforeCleanup cleanupEvents afterCleanup := by
    rw [beforeCount]
    exact actor_recorded_filesystem (Eq.mp (congrArg (fun raw => ActorHistoryWith runtime
      source.allocation.earlier.source.inputActor (SourceReturnAt runtime all source.allocation.earlier.source.inputActor)
      (source.allocation.earlier.source.input.events.length + 1 +
        (source.allocation.earlier.post.map Program.filesystemEvent).length + source.point.createdAfter.length + workRaw.length)
      beforeCleanup raw afterCleanup) cleanupTrace) cleanupHistory)
  exact ⟨{
    beforeRaw
    cleanupEvents
    chunks := Eq.mp (congrArg (fun raw => PrimitiveFilesystem.Chunks
      (inside.map Program.filesystemPrefixEvent) raw) cleanupTrace) originalCleanupChunks
    trace := by
      exact source.eventTrace.trans (by
        rw [source.point.trace, rawTrace, cleanupTrace]
        simp only [beforeRaw, List.append_assoc, List.cons_append])
    beforeCleanup
    afterCleanup
    history := cleanupHistory
    active := lift_prefix_exact actualPrefix
    directory
    workRaw
    workChunks
    beforeTrace := rfl }⟩

end LeanCage.Host.Kernel
