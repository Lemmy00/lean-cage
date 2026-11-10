import FilesystemPendingPrefixPhases

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.caller: Runtime and filesystem actions retain their individual actual
-- rows while a VM helper is still running; the current write has no observed return.
structure PendingProgramPhase {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    (initial : World) (all : List (ActorTick runtime)) (tick : ActorTick runtime)
    (actor : ActorId) (engine : EngineState) (request : Request) {α : Type} (program : Program α) where
  source : SelectedActorHistory runtime initial all tick actor engine
  pending : EntrypointWriterPrefix.PendingCut engine request
  rawBefore : List Program.Event
  before : World
  events : List Program.Event
  trace : engine.events = rawBefore ++ events
  leading : ActorHistoryWith runtime actor (SourceReturnAt runtime all actor) 0
    (source.launch.tick.after.project (.initialFrom (PrimitiveFilesystem.lower Entrypoint.run)
      source.launch.references source.launch.closeExec source.launch.workingDirectory)) rawBefore before
  active : Program.Prefix (PrimitiveFilesystem.lower program) (events ++ [.lost (.filesystem request)])
  actual : ActorHistoryWith runtime actor (SourceReturnAt runtime all actor) rawBefore.length
    before events (tick.before.project engine)

-- §AR-host-boundary.primitives: This is a source-derived exact shared-history slice,
-- not a VMM/runtime lifetime frame or a separately chosen helper execution.
theorem pending_program_prefix_phase_exact {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request}
    (history : SelectedActorHistory runtime initial all tick actor engine)
    (pending : EntrypointWriterPrefix.PendingCut engine request)
    {α : Type} (program : Program α) {context inside : List Program.Event}
    (source : Program.Prefix program (inside ++ [Program.filesystemPrefixEvent (request, none)]))
    (trace : pending.occurrence.logicalBefore = context ++ inside) :
    ∃ phase : PendingProgramPhase runtime initial all tick actor engine request program,
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
  have engineTrace : engine.events = rawBefore ++ rawInside := pending.rawTrace.trans rawTrace
  have actualHistory := history.history
  rw [engineTrace] at actualHistory
  obtain ⟨before, leading, tail⟩ := actor_with_split rawBefore _ actualHistory
  exact ⟨⟨history, pending, rawBefore, before, rawInside, engineTrace, leading, lowered,
    by simpa only [Nat.zero_add] using tail⟩, rfl, rfl⟩

theorem pending_program_prefix_phase {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request}
    (history : SelectedActorHistory runtime initial all tick actor engine)
    (pending : EntrypointWriterPrefix.PendingCut engine request)
    {α : Type} (program : Program α) {context inside : List Program.Event}
    (source : Program.Prefix program (inside ++ [Program.filesystemPrefixEvent (request, none)]))
    (trace : pending.occurrence.logicalBefore = context ++ inside) :
    Nonempty (PendingProgramPhase runtime initial all tick actor engine request program) := by
  obtain ⟨phase, sameSource, samePending⟩ := pending_program_prefix_phase_exact history pending program source trace
  exact ⟨phase⟩

end LeanCage.Host.Kernel
