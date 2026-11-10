import FilesystemPrimitivePrefixPhases
import FilesystemPendingBorrowing

namespace LeanCage.Host.Kernel
open Filesystem

structure PrimitiveBeforePhase {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    {α : Type} (program : Filesystem.Program α) where
  rawBefore : List Program.Event
  before : World
  earlier : List (Request × Reply)
  trace : engine.events = rawBefore ++ earlier.map Program.filesystemEvent
  history : RecordedHistory kernel (fun ordinal query reply =>
    SourceReturnAt runtime all actor ordinal Reply (.filesystem query) reply)
    rawBefore.length before earlier (tick.before.project engine)
  active : Prefix program.lower (Publication.completed earlier ++ [(request, none)])

-- §FS-host-boundary.ownership: Reconstruct this interrupted helper only up
-- to the real current syscall's input. Earlier probes and returned calls
-- keep their original global origins; no current reply is used.
theorem primitive_filesystem_before_phase {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    (primary : request = adapter.occurrence.primary)
    {α : Type} (program : Filesystem.Program α) {context inside : List Program.Event}
    (source : Program.Prefix (Program.liftFilesystem program)
      (inside ++ [Program.filesystemPrefixEvent (request, none)]))
    (trace : adapter.occurrence.logicalBefore = context ++ inside) :
    Nonempty (PrimitiveBeforePhase adapter program) := by
  have chunks := PrimitiveFilesystem.reached_chunks adapter.occurrence.reached
  rw [trace] at chunks
  obtain ⟨rawBefore, rawInside, leadingChunks, insideChunks, rawTrace⟩ :=
    PrimitiveFilesystem.chunks_split context inside chunks
  have rawAdapter : Program.Prefix (PrimitiveFilesystem.lowerEffect (.filesystem request))
      (adapter.occurrence.inside.map Program.filesystemPrefixEvent ++ [Program.filesystemPrefixEvent (request, none)]) := by
    have active := Program.lift_filesystem_prefix (prefix_last_pending adapter.occurrence.adapter)
    rw [← primary] at active
    simpa only [PrimitiveFilesystem.lowerEffect, List.map_append, List.map_singleton] using active
  have lowered := PrimitiveFilesystem.pending_chunks_prefix (.filesystem request) source insideChunks rawAdapter
  rw [PrimitiveFilesystem.lower_lift_filesystem] at lowered
  have lowered : Program.Prefix (Program.liftFilesystem program.lower)
      ((rawInside ++ adapter.occurrence.inside.map Program.filesystemPrefixEvent) ++
        [Program.filesystemPrefixEvent (request, none)]) := by
    simpa only [List.append_assoc] using lowered
  obtain ⟨earlier, active, earlierTrace⟩ := selected_filesystem_source lowered
  have engineTrace : engine.events = rawBefore ++ earlier.map Program.filesystemPrefixEvent := by
    rw [adapter.occurrence.trace, rawTrace, List.append_assoc, earlierTrace]
  have history := adapter.source.history
  rw [engineTrace] at history
  obtain ⟨before, leading, tail⟩ := actor_with_split rawBefore _ history
  obtain ⟨completed, completedTrace, recorded⟩ := actor_raw_filesystem tail
  have exactEvents : earlier.map Program.filesystemPrefixEvent = completed.map Program.filesystemEvent := by
    rw [completedTrace, List.map_map]
    rfl
  have recorded : RecordedHistory kernel (fun ordinal query reply =>
      SourceReturnAt runtime all actor ordinal Reply (.filesystem query) reply)
      rawBefore.length before completed (tick.before.project engine) := by
    have actual : ActorHistoryWith runtime actor (SourceReturnAt runtime all actor) rawBefore.length before
        (completed.map Program.filesystemEvent) (tick.before.project engine) := by
      simpa only [Nat.zero_add, exactEvents] using tail
    exact actor_recorded_filesystem actual
  refine ⟨⟨rawBefore, before, completed, engineTrace.trans (congrArg (rawBefore ++ ·) exactEvents), recorded, ?_⟩⟩
  simpa only [completedTrace, Publication.completed] using active

end LeanCage.Host.Kernel
