import FilesystemCleanupTraversal

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: This selected cleanup's exact completed
-- prefix and pending source operands produce its current parent. Guard
-- probes are separate rows, and final root removal remains a distinct case.
theorem CleanupStageSegment.parent_or_final_source {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel)
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    {call : PublicationCleanup.Host adapter.occurrence.logicalBefore request} {limit : Nat}
    {source : CleanupStageContinuation runtime initial all call limit (tick.before.project engine)}
    (segment : CleanupStageSegment source)
    (guards : source.earlier.guards = adapter.occurrence.inside.map Program.filesystemPrefixEvent)
    (eventTrace : engine.events = source.earlier.source.input.events ++
      .returned (.filesystem source.opening.request) source.opening.reply ::
        (source.earlier.post.map Program.filesystemEvent ++ source.earlier.remaining ++ source.earlier.guards))
    (unlink : request.op = .unlinkAt) {family : Family} {scope : ObjectId}
    (opens : PrivateDirectoryOpens kernel (fun ordinal query reply before after =>
      SourceReturnAt runtime all source.earlier.source.inputActor ordinal Reply (.filesystem query) reply before after ∧
        ordinal < engine.events.length) family)
    (privateRoot : family source.earlier.source.opening.handle.object = some scope) :
    (∃ parent, engine.references request.first = some parent ∧ family parent.object = some scope) ∨
      Nonempty (Lowered.FinalCleanupFrontier call.source.attempt.context.parent call.source.attempt.context.stage
        call.source.effective call.source.attempt.inside request) := by
  obtain ⟨middle, cleanupHistory, guarded⟩ := actor_with_split segment.cleanupRaw source.earlier.guards segment.actorHistory
  have guardedFrame := actor_retaining_event_handles descriptors guarded (by
    rw [guards]
    exact adapter_namespace_prefix_retaining adapter (.inr (.inr (.inl unlink))))
  have bound : segment.beforeRaw.length + segment.cleanupRaw.length ≤ engine.events.length := by
    have length := congrArg List.length (segment.event_trace eventTrace)
    have rawLength := congrArg List.length segment.trace
    simp only [List.length_append, List.length_map] at length rawLength
    omega
  obtain ⟨frontier⟩ := Publication.cleanup_frontier _ _ _ call.source.attempt.active unlink
  rcases Lowered.cleanup_parent_or_final_source descriptors source.earlier.source.inputActor
      (SourceReturnAt runtime all source.earlier.source.inputActor) engine.events.length opens frontier
      segment.chunks cleanupHistory bound segment.directory privateRoot segment.distinct (by
        intro inner
        rw [← guardedFrame]
        exact segment.current_directory descriptors unlink inner) with privateParent | finalRoot
  · obtain ⟨parent, reference, scope⟩ := privateParent
    exact .inl ⟨parent, by
      change (tick.before.project engine).handles request.first = some parent
      rw [guardedFrame]
      exact reference, scope⟩
  · exact .inr finalRoot

-- §AR-host-boundary.interfaces: Retain the original current-parent result.
theorem CleanupStageSegment.parent_or_final {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel)
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    {call : PublicationCleanup.Host adapter.occurrence.logicalBefore request} {limit : Nat}
    {source : CleanupStageContinuation runtime initial all call limit (tick.before.project engine)}
    (segment : CleanupStageSegment source)
    (guards : source.earlier.guards = adapter.occurrence.inside.map Program.filesystemPrefixEvent)
    (eventTrace : engine.events = source.earlier.source.input.events ++
      .returned (.filesystem source.opening.request) source.opening.reply ::
        (source.earlier.post.map Program.filesystemEvent ++ source.earlier.remaining ++ source.earlier.guards))
    (unlink : request.op = .unlinkAt) {family : Family} {scope : ObjectId}
    (opens : PrivateDirectoryOpens kernel (fun ordinal query reply before after =>
      SourceReturnAt runtime all source.earlier.source.inputActor ordinal Reply (.filesystem query) reply before after ∧
        ordinal < engine.events.length) family)
    (privateRoot : family source.earlier.source.opening.handle.object = some scope) :
    (∃ parent, engine.references request.first = some parent ∧ family parent.object = some scope) ∨
      Lowered.FinalStageRemoval call.source.attempt.context.stage request := by
  rcases segment.parent_or_final_source descriptors adapter guards eventTrace unlink opens privateRoot with privateParent | finalSource
  · exact .inl privateParent
  · obtain ⟨finalSource⟩ := finalSource
    exact .inr finalSource.operation

end LeanCage.Host.Kernel
