import FilesystemLoweredPhases

namespace LeanCage.Host.Kernel
open Filesystem

structure PrimitivePhaseAt {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    (initial : World) (ticks : List (ActorTick runtime)) (tick : ActorTick runtime)
    (actor : ActorId) (engine : EngineState) {α : Type} (program : Filesystem.Program α) (value : α) where
  source : SelectedActorHistory runtime initial ticks tick actor engine
  rawBefore : List Program.Event
  events : List (Request × Reply)
  rawAfter : List Program.Event
  trace : engine.events = rawBefore ++ events.map Program.filesystemEvent ++ rawAfter
  before : World
  after : World
  leading : ActorHistoryWith runtime actor (SourceReturnAt runtime ticks actor) 0
    (source.launch.tick.after.project (.initialFrom (PrimitiveFilesystem.lower Entrypoint.run)
      source.launch.references source.launch.closeExec source.launch.workingDirectory)) rawBefore before
  actual : RecordedRun kernel (fun index request reply =>
    SourceReturnAt runtime ticks actor index Reply (.filesystem request) reply) rawBefore.length
    program.lower before events after value
  tail : ActorHistoryWith runtime actor (SourceReturnAt runtime ticks actor)
    (rawBefore.length + events.length) after rawAfter (tick.before.project engine)

structure PrimitivePhaseChunked {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {ticks : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial ticks tick actor engine request observed)
    {α : Type} (program : Filesystem.Program α) (value : α) (following : List Program.Event) where
  phase : PrimitivePhaseAt runtime initial ticks tick actor engine program value
  rawTail : List Program.Event
  chunks : PrimitiveFilesystem.Chunks following rawTail
  suffix : phase.rawAfter = rawTail ++ adapter.occurrence.inside.map Program.filesystemPrefixEvent

-- §AR-host-boundary.primitives: A source helper return is connected to its exact expanded raw
-- chunk and the same native handoff, actor states, global journal and selected later call.
theorem primitive_filesystem_phase {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {ticks : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial ticks tick actor engine request observed)
    {α : Type} {program : Filesystem.Program α} {value : α} {events : List (Request × Reply)}
    {context following : List Program.Event} (returned : Returns program events value)
    (trace : adapter.occurrence.logicalBefore = context ++ events.map Program.filesystemEvent ++ following) :
    Nonempty (PrimitivePhaseChunked adapter program value following) := by
  have chunks := PrimitiveFilesystem.reached_chunks adapter.occurrence.reached
  rw [trace, List.append_assoc] at chunks
  obtain ⟨first, rest, leadingChunks, remainingChunks, firstTrace⟩ := PrimitiveFilesystem.chunks_split context _ chunks
  obtain ⟨inside, last, phaseChunks, tailChunks, lastTrace⟩ :=
    PrimitiveFilesystem.chunks_split (events.map Program.filesystemEvent) following remainingChunks
  obtain ⟨raw, actual, rawTrace⟩ := PrimitiveFilesystem.chunks_filesystem_returns returned phaseChunks
  let final := last ++ adapter.occurrence.inside.map Program.filesystemPrefixEvent
  have full : engine.events = first ++ raw.map Program.filesystemEvent ++ final := by
    rw [adapter.occurrence.trace, firstTrace, lastTrace, rawTrace]
    simp only [final, List.append_assoc]
  have history := adapter.source.history
  rw [full, List.append_assoc] at history
  obtain ⟨before, initialHistory, active⟩ := actor_with_split first _ history
  obtain ⟨after, phase, tail⟩ := actor_with_split (raw.map Program.filesystemEvent) final active
  refine ⟨⟨⟨adapter.source, first, raw, final, full, before, after, initialHistory,
    ⟨actual, ?_⟩, ?_⟩, last, tailChunks, rfl⟩⟩
  · simpa only [Nat.zero_add] using actor_recorded_filesystem phase
  · simpa only [List.length_map, Nat.zero_add] using tail

end LeanCage.Host.Kernel
