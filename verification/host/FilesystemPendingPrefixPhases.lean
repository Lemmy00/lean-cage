import EntrypointPendingWriter
import FilesystemPrimitivePrefixPhases
import FilesystemRunningHistory

namespace LeanCage.Host.Kernel
open Filesystem

private theorem before_pending {α : Type} {program : Filesystem.Program α} (earlier : List (Request × Reply))
    {request : Request} (source : Prefix program (Publication.completed earlier ++ [(request, none)])) :
    Prefix program (Publication.completed earlier) := by
  induction earlier generalizing program with
  | nil => exact .empty _
  | cons event earlier ih =>
    rcases event with ⟨operation, reply⟩
    change Prefix program ((operation, some reply) :: (Publication.completed earlier ++ [(request, none)])) at source
    cases source with
    | returned operation next reply rest continued => exact .returned operation next reply _ (ih continued)

private theorem raw_history_physical_prefix {kernel : Contract} {origin : RawOrigin} {ordinal : Nat}
    {α : Type} {program : Filesystem.Program α} {before after : World} {earlier : List (Request × Reply)}
    (source : Prefix program (Publication.completed earlier))
    (history : RawHistory kernel.step kernel.interference origin ordinal before earlier after) :
    PhysicalPrefix kernel program before (Publication.completed earlier) after := by
  induction history generalizing program with
  | nil => exact .stop _ _
  | environment actual tail ih => exact .environment actual (ih source)
  | call actual sampled tail ih =>
    cases source with
    | returned request next reply rest continued => exact .returned actual (ih continued)

-- §FS-host-boundary.caller: This current helper state is before the pending write has any
-- application reply. Each preceding operation still samples the SAME global native history.
structure PendingPrefixPhase {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    (initial : World) (all : List (ActorTick runtime)) (tick : ActorTick runtime)
    (actor : ActorId) (engine : EngineState) (request : Request) {α : Type} (program : Filesystem.Program α) where
  source : SelectedActorHistory runtime initial all tick actor engine
  pending : EntrypointWriterPrefix.PendingCut engine request
  rawBefore : List Program.Event
  before : World
  earlier : List (Request × Reply)
  trace : engine.events = rawBefore ++ earlier.map Program.filesystemEvent
  leading : ActorHistoryWith runtime actor (SourceReturnAt runtime all actor) 0
    (source.launch.tick.after.project (.initialFrom (PrimitiveFilesystem.lower Entrypoint.run)
      source.launch.references source.launch.closeExec source.launch.workingDirectory)) rawBefore before
  active : Prefix program.lower (Publication.completed earlier ++ [(request, none)])
  sampled : RawHistory kernel.step kernel.interference (SourceRawAt runtime all actor) rawBefore.length
    before earlier (tick.before.project engine)
  actual : PhysicalPrefix kernel program.lower before (Publication.completed earlier) (tick.before.project engine)

-- §AR-host-boundary.primitives: No current kernel write step, acknowledged count, final ACK
-- or future engine return is assumed when deriving the state of this actual source helper.
theorem pending_filesystem_prefix_phase_exact {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request}
    (history : SelectedActorHistory runtime initial all tick actor engine)
    (pending : EntrypointWriterPrefix.PendingCut engine request)
    {α : Type} (program : Filesystem.Program α) {context inside : List Program.Event}
    (source : Program.Prefix (Program.liftFilesystem program)
      (inside ++ [Program.filesystemPrefixEvent (request, none)]))
    (trace : pending.occurrence.logicalBefore = context ++ inside) :
    ∃ phase : PendingPrefixPhase runtime initial all tick actor engine request program,
      phase.source = history ∧ phase.pending = pending := by
  have chunks := PrimitiveFilesystem.reached_chunks pending.occurrence.reached
  rw [trace] at chunks
  obtain ⟨rawBefore, rawInside, leadingChunks, insideChunks, rawTrace⟩ :=
    PrimitiveFilesystem.chunks_split context inside chunks
  have rawAdapter : Program.Prefix (PrimitiveFilesystem.lowerEffect (.filesystem request))
      [Program.filesystemPrefixEvent (request, none)] := by
    have active := Program.lift_filesystem_prefix pending.occurrence.adapter
    rw [← pending.primary, pending.noGuards] at active
    simpa only [PrimitiveFilesystem.lowerEffect, List.nil_append, List.map_nil, List.map_singleton] using active
  have lowered := PrimitiveFilesystem.pending_chunks_prefix (.filesystem request) source insideChunks rawAdapter
  rw [PrimitiveFilesystem.lower_lift_filesystem] at lowered
  obtain ⟨earlier, active, earlierTrace⟩ := selected_filesystem_source lowered
  have engineTrace : engine.events = rawBefore ++ earlier.map Program.filesystemPrefixEvent :=
    pending.rawTrace.trans (rawTrace.trans (congrArg (rawBefore ++ ·) earlierTrace))
  have actualHistory := history.history
  rw [engineTrace] at actualHistory
  obtain ⟨before, leading, tail⟩ := actor_with_split rawBefore _ actualHistory
  obtain ⟨completed, completedTrace, recorded⟩ := actor_raw_filesystem tail
  have recorded : RawHistory kernel.step kernel.interference (SourceRawAt runtime all actor)
      rawBefore.length before completed (tick.before.project engine) := by
    simpa only [Nat.zero_add] using recorded
  have exactTrace : engine.events = rawBefore ++ completed.map Program.filesystemEvent :=
    engineTrace.trans (congrArg (rawBefore ++ ·) (by rw [completedTrace, List.map_map]; rfl))
  have original : Prefix program.lower (Publication.completed completed ++ [(request, none)]) := by
    simpa only [completedTrace, Publication.completed] using active
  exact ⟨⟨history, pending, rawBefore, before, completed, exactTrace, leading, original, recorded,
    raw_history_physical_prefix (before_pending completed original) recorded⟩, rfl, rfl⟩

theorem pending_filesystem_prefix_phase {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request}
    (history : SelectedActorHistory runtime initial all tick actor engine)
    (pending : EntrypointWriterPrefix.PendingCut engine request)
    {α : Type} (program : Filesystem.Program α) {context inside : List Program.Event}
    (source : Program.Prefix (Program.liftFilesystem program)
      (inside ++ [Program.filesystemPrefixEvent (request, none)]))
    (trace : pending.occurrence.logicalBefore = context ++ inside) :
    Nonempty (PendingPrefixPhase runtime initial all tick actor engine request program) := by
  obtain ⟨phase, sameSource, samePending⟩ := pending_filesystem_prefix_phase_exact history pending program source trace
  exact ⟨phase⟩

end LeanCage.Host.Kernel
