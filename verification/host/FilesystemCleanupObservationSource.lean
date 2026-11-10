import FilesystemCleanupObservations

namespace LeanCage.Host.Kernel
open Filesystem

theorem CleanupStageSegment.guard_count {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {tick : ActorTick runtime}
    {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    {call : PublicationCleanup.Host adapter.occurrence.logicalBefore request} {limit : Nat}
    {source : CleanupStageContinuation runtime initial all call limit (tick.before.project engine)}
    (segment : CleanupStageSegment source)
    (guards : source.earlier.guards = adapter.occurrence.inside.map Program.filesystemPrefixEvent)
    (eventTrace : engine.events = source.earlier.source.input.events ++
      .returned (.filesystem source.opening.request) source.opening.reply ::
        (source.earlier.post.map Program.filesystemEvent ++ source.earlier.remaining ++ source.earlier.guards)) :
    segment.beforeRaw.length + segment.cleanupRaw.length = adapter.occurrence.rawBefore.length := by
  have count := congrArg List.length (segment.event_trace eventTrace)
  have rawCount := congrArg List.length segment.trace
  have sourceCount := congrArg List.length adapter.occurrence.trace
  have guardCount := congrArg List.length guards
  simp only [List.length_append, List.length_map] at count rawCount sourceCount guardCount
  omega

-- §FS-host-boundary.lookup: The raw source supplies the selected nested
-- parent's actual stat observation before this call's lookup guard. Its
-- retained reference survives those guards, without a whole cleanup frame.
theorem CleanupStageSegment.observed_parent_or_final {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
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
    Nonempty (ObservedUnlinkParent kernel (fun ordinal query reply =>
      SourceReturnAt runtime all source.earlier.source.inputActor ordinal Reply (.filesystem query) reply)
      (segment.beforeRaw.length + segment.cleanupRaw.length) (tick.before.project engine)
      call.source.attempt.context.parent.uid request family scope) ∨
      Nonempty (Lowered.FinalCleanupFrontier call.source.attempt.context.parent call.source.attempt.context.stage
        call.source.effective call.source.attempt.inside request) := by
  obtain ⟨middle, cleanupHistory, guarded⟩ := actor_with_split segment.cleanupRaw source.earlier.guards segment.actorHistory
  have guardedFrame := actor_retaining_event_handles descriptors guarded (by
    rw [guards]
    exact adapter_namespace_prefix_retaining adapter (.inr (.inr (.inl unlink))))
  have bound : segment.beforeRaw.length + segment.cleanupRaw.length ≤ engine.events.length := by
    rw [segment.guard_count adapter guards eventTrace]
    have count := congrArg List.length adapter.occurrence.trace
    simp only [List.length_append, List.length_map] at count
    omega
  obtain ⟨frontier⟩ := Publication.cleanup_frontier _ _ _ call.source.attempt.active unlink
  have observationPrivate : family segment.observation.handle.object = some scope := by
    rw [segment.sameObserved]
    exact privateRoot
  rcases Lowered.cleanup_observed_or_final descriptors source.earlier.source.inputActor
      (SourceReturnAt runtime all source.earlier.source.inputActor) engine.events.length opens frontier
      segment.chunks cleanupHistory bound segment.observation observationPrivate segment.distinct (by
        intro inner
        rw [← guardedFrame, segment.sameObserved]
        exact segment.current_directory descriptors unlink inner) with privateParent | finalRoot
  · obtain ⟨result⟩ := privateParent
    have live : (tick.before.project engine).handles result.directory.fd = some result.observation.handle := by
      rw [guardedFrame]
      exact result.observation.live
    exact .inl ⟨{result with observation := result.observation.advance live (Nat.le_refl _)}⟩
  · exact .inr finalRoot

end LeanCage.Host.Kernel
