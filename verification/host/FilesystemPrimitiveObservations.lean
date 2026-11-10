import FilesystemPrimitiveChunks
import FilesystemPrimitiveRecording
import FilesystemDirectoryObservations

namespace LeanCage.Host.Kernel
open Filesystem

structure PrimitiveObservationAt {kernel : Contract} (runtime : PrimitiveActorRuntime kernel)
    (initial : World) (ticks : List (ActorTick runtime)) (tick : ActorTick runtime)
    (actor : ActorId) (engine : EngineState) {β : Type} (effect : Effect β) (reply : β) where
  source : SelectedActorHistory runtime initial ticks tick actor engine
  rawBefore : List Program.Event
  rawAfter : List Program.Event
  trace : engine.events = rawBefore ++ .returned effect reply :: rawAfter
  before : World
  after : World
  leading : ActorHistoryWith runtime actor (SourceReturnAt runtime ticks actor) 0
    (source.launch.tick.after.project (.initialFrom (PrimitiveFilesystem.lower Entrypoint.run)
      source.launch.references source.launch.closeExec source.launch.workingDirectory)) rawBefore before
  actual : ActorOperation runtime actor effect (some reply) before after
  sampled : SourceReturnAt runtime ticks actor rawBefore.length β effect reply before after
  tail : ActorHistoryWith runtime actor (SourceReturnAt runtime ticks actor) (rawBefore.length + 1)
    after rawAfter (tick.before.project engine)

structure PrimitiveObservationChunked {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {ticks : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial ticks tick actor engine request observed)
    {β : Type} (effect : Effect β) (reply : β) (following : List Program.Event) where
  observation : PrimitiveObservationAt runtime initial ticks tick actor engine effect reply
  rawTail : List Program.Event
  chunks : PrimitiveFilesystem.Chunks following rawTail
  suffix : observation.rawAfter = rawTail ++ adapter.occurrence.inside.map Program.filesystemPrefixEvent

theorem PrimitiveObservationChunked.before_guard {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {ticks : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    {adapter : PrimitiveAdapterAt runtime initial ticks tick actor engine request observed}
    {β : Type} {effect : Effect β} {reply : β} {following : List Program.Event}
    (source : PrimitiveObservationChunked adapter effect reply following) :
    source.observation.rawBefore.length < adapter.occurrence.rawBefore.length := by
  have first := congrArg List.length source.observation.trace
  have second := congrArg List.length adapter.occurrence.trace
  have remaining := congrArg List.length source.suffix
  simp only [List.length_append, List.length_cons, List.length_map] at first second remaining
  omega

-- §FS-host-boundary.ownership: UID/stat and other unchanged source calls are extracted from
-- their genuine completed raw chunks, retaining the same native handoff and global provenance.
theorem primitive_observation_chunked {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {ticks : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial ticks tick actor engine request observed)
    {β : Type} {effect : Effect β} {reply : β} {context following : List Program.Event}
    (trace : adapter.occurrence.logicalBefore = context ++ .returned effect reply :: following)
    (identity : PrimitiveFilesystem.lowerEffect effect = Program.effect effect) :
    Nonempty (PrimitiveObservationChunked adapter effect reply following) := by
  obtain ⟨first, last, leading, trailing, rawTrace⟩ := PrimitiveFilesystem.chunks_selected_identity
    (PrimitiveFilesystem.reached_chunks adapter.occurrence.reached) trace identity
  let remaining := last ++ adapter.occurrence.inside.map Program.filesystemPrefixEvent
  have full : engine.events = first ++ .returned effect reply :: remaining :=
    adapter.occurrence.trace.trans (by
      simpa only [remaining, List.append_assoc, List.cons_append] using
        congrArg (· ++ adapter.occurrence.inside.map Program.filesystemPrefixEvent) rawTrace)
  have history : ActorHistoryWith runtime actor (SourceReturnAt runtime ticks actor) 0
      (adapter.source.launch.tick.after.project (.initialFrom (PrimitiveFilesystem.lower Entrypoint.run)
        adapter.source.launch.references adapter.source.launch.closeExec adapter.source.launch.workingDirectory))
      (first ++ .returned effect reply :: remaining) (tick.before.project engine) := by
    simpa only [full] using adapter.source.history
  obtain ⟨afterLeading, leading, active⟩ := actor_with_split first _ history
  obtain ⟨before, after, environment, operation, sampled, tail⟩ := actor_with_head active
  have completeLeading : ActorHistoryWith runtime actor (SourceReturnAt runtime ticks actor) 0
      (adapter.source.launch.tick.after.project (.initialFrom (PrimitiveFilesystem.lower Entrypoint.run)
        adapter.source.launch.references adapter.source.launch.closeExec adapter.source.launch.workingDirectory))
      first before := by
    simpa only [List.append_nil] using actor_with_append leading environment
  let observation : PrimitiveObservationAt runtime initial ticks tick actor engine effect reply := {
    source := adapter.source
    rawBefore := first
    rawAfter := remaining
    trace := full
    before
    after
    leading := completeLeading
    actual := operation
    sampled := by simpa only [Nat.zero_add] using sampled
    tail := by simpa only [Nat.zero_add] using tail }
  exact ⟨⟨observation, last, trailing, rfl⟩⟩

theorem primitive_observation {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {ticks : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial ticks tick actor engine request observed)
    {β : Type} {effect : Effect β} {reply : β} {context following : List Program.Event}
    (trace : adapter.occurrence.logicalBefore = context ++ .returned effect reply :: following)
    (identity : PrimitiveFilesystem.lowerEffect effect = Program.effect effect) :
    Nonempty (PrimitiveObservationAt runtime initial ticks tick actor engine effect reply) := by
  obtain ⟨chunked⟩ := primitive_observation_chunked adapter trace identity
  exact ⟨chunked.observation⟩

theorem primitive_stat_information {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel) {initial : World} {ticks : List (ActorTick runtime)}
    {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState} {fd : UInt64} {reply : Reply}
    (source : PrimitiveObservationAt runtime initial ticks tick actor engine
      (.filesystem { op := .stat, first := fd }) reply) {handle : Handle} {information : Stat}
    (live : source.before.handles fd = some handle) (parsed : parseStat reply = some information) :
    source.before.information handle.object = some information :=
  descriptors.stat_actual _ _ _ _ _ _ source.actual rfl live parsed

theorem primitive_uid_is_host {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {hostUid : Nat} (accounts : AccountContract kernel hostUid)
    {initial : World} {ticks : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {reply : Reply}
    (source : PrimitiveObservationAt runtime initial ticks tick actor engine (.filesystem { op := .euid }) reply)
    (successful : nativeError reply = false) (empty : reply.2 = .empty) : reply.1.toNat = hostUid :=
  accounts.effective _ _ _ _ source.actual rfl successful empty

end LeanCage.Host.Kernel
