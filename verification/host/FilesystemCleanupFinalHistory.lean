import FilesystemCleanupBeforeRoot
import FilesystemCleanupLeading

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.ownership: The final removal's exact logical frontier
-- reconstructs the SAME earlier raw transcript. All prior unlinks have
-- captured private parents, including their ignored error replies.
theorem CleanupStageSegment.final_replies_private {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
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
    (privateRoot : family source.earlier.source.opening.handle.object = some scope)
    (finalSource : Lowered.FinalCleanupFrontier call.source.attempt.context.parent call.source.attempt.context.stage
      call.source.effective call.source.attempt.inside request) :
    PrivateUnlinkReplies (kernel := kernel) (SourceReturnAt runtime all source.earlier.source.inputActor)
      family scope segment.beforeRaw.length segment.events := by
  have logicalTrace : call.source.attempt.inside.map Program.filesystemPrefixEvent =
      finalSource.replies.map Program.filesystemEvent := by
    exact (congrArg (List.map Program.filesystemPrefixEvent) finalSource.trace).trans (completed_filesystem_events _)
  have chunks : PrimitiveFilesystem.Chunks (finalSource.replies.map Program.filesystemEvent) segment.cleanupRaw := by
    exact Eq.mp (congrArg (fun logical => PrimitiveFilesystem.Chunks logical segment.cleanupRaw) logicalTrace) segment.chunks
  obtain ⟨middle, bodyHistory, guarded⟩ := actor_with_split segment.cleanupRaw source.earlier.guards segment.actorHistory
  obtain ⟨bodyEvents, bodySource, bodyTrace⟩ := PrimitiveFilesystem.chunks_filesystem_returns finalSource.returned chunks
  have bodyRun : RecordedRun kernel (fun ordinal query reply =>
      SourceReturnAt runtime all source.earlier.source.inputActor ordinal Reply (.filesystem query) reply)
      segment.beforeRaw.length (cleanupBeforeRoot call.source.attempt.context.parent call.source.attempt.context.stage
        call.source.effective).lower segment.world bodyEvents middle () :=
    ⟨bodySource, actor_recorded_filesystem (bodyTrace ▸ bodyHistory)⟩
  have bound : segment.beforeRaw.length + bodyEvents.length ≤ engine.events.length := by
    have count := congrArg List.length (segment.event_trace eventTrace)
    have rawCount := congrArg List.length segment.trace
    have bodyCount := congrArg List.length bodyTrace
    simp only [List.length_append, List.length_map] at count rawCount bodyCount
    omega
  have bodyOwned := actual_cleanup_before_root_replies (runtime := runtime) descriptors source.earlier.source.inputActor
    (SourceReturnAt runtime all source.earlier.source.inputActor) engine.events.length opens bodyRun bound segment.directory privateRoot
  have guarded : ActorHistoryWith runtime source.earlier.source.inputActor
      (SourceReturnAt runtime all source.earlier.source.inputActor)
      (segment.beforeRaw.length + segment.cleanupRaw.length) middle
      (adapter.occurrence.inside.map Program.filesystemPrefixEvent) (tick.before.project engine) := guards ▸ guarded
  obtain ⟨guardEvents, guardTrace, guardHistory⟩ := actor_raw_filesystem guarded
  have guardMap : source.earlier.guards = guardEvents.map Program.filesystemEvent := by
    rw [guards, guardTrace, List.map_map]
    rfl
  have guardOwned : PrivateUnlinkReplies (kernel := kernel) (SourceReturnAt runtime all source.earlier.source.inputActor)
      family scope (segment.beforeRaw.length + bodyEvents.length) guardEvents := by
    apply no_unlink_replies
    intro pair member removing
    have inGuards : Program.filesystemEvent pair ∈ source.earlier.guards := by
      rw [guardMap]
      exact List.mem_map.mpr ⟨pair, member, rfl⟩
    have quiet := adapter_namespace_prefix_nondestructive adapter (.inr (.inr (.inl unlink)))
      (Program.filesystemEvent pair) (guards ▸ inGuards)
    exact quiet (.inl removing)
  have exactEvents : segment.events = bodyEvents ++ guardEvents := by
    apply PrimitiveFilesystem.filesystem_events_injective
    rw [segment.trace, bodyTrace, guardMap, List.map_append]
  exact exactEvents ▸ private_unlink_replies_append bodyOwned guardOwned

-- §FS-host-boundary.ownership: An earlier removal is matched by its source
-- ordinal in this same actor transcript. It cannot use another equal call
-- or a later descriptor reuse as evidence for the parent it actually had.
theorem CleanupStageSegment.captured_previous_unlink {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (descriptors : DescriptorContract kernel)
    {initial : World} {final : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) all final)
    {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState} {request : Request} {observed : Option Reply}
    (adapter : PrimitiveAdapterAt runtime initial all tick actor engine request observed)
    {call : PublicationCleanup.Host adapter.occurrence.logicalBefore request} {limit : Nat}
    {source : CleanupStageContinuation runtime initial all call limit (tick.before.project engine)}
    (segment : CleanupStageSegment source) (sameActor : source.earlier.source.inputActor = actor)
    (guards : source.earlier.guards = adapter.occurrence.inside.map Program.filesystemPrefixEvent)
    (eventTrace : engine.events = source.earlier.source.input.events ++
      .returned (.filesystem source.opening.request) source.opening.reply ::
        (source.earlier.post.map Program.filesystemEvent ++ source.earlier.remaining ++ source.earlier.guards))
    (unlink : request.op = .unlinkAt) {family : Family} {scope : ObjectId}
    (opens : PrivateDirectoryOpens kernel (fun ordinal query reply before after =>
      SourceReturnAt runtime all source.earlier.source.inputActor ordinal Reply (.filesystem query) reply before after ∧
        ordinal < engine.events.length) family)
    (privateRoot : family source.earlier.source.opening.handle.object = some scope)
    (finalSource : Lowered.FinalCleanupFrontier call.source.attempt.context.parent call.source.attempt.context.stage
      call.source.effective call.source.attempt.inside request)
    {ordinal : Nat} {query : Request} {reply : Reply} {before after : World}
    (sample : SourceReturnAt runtime all actor ordinal Reply (.filesystem query) reply before after)
    (atEvent : engine.events[ordinal]? = some (.returned (.filesystem query) reply))
    (sinceBirth : source.root.use.engine.events.length + 1 ≤ ordinal) (removing : query.op = .unlinkAt) :
    ∃ parent, before.handles query.first = some parent ∧ family parent.object = some scope ∧
      Directories.component query.left = true := by
  have full := segment.event_trace eventTrace
  have afterBefore : segment.beforeRaw.length ≤ ordinal := by
    by_cases earlier : ordinal < segment.beforeRaw.length
    · have selected : segment.beforeRaw[ordinal]? = some (.returned (.filesystem query) reply) := by
        simpa only [full, List.getElem?_append_left earlier] using atEvent
      have inDropped : (segment.beforeRaw.drop (source.root.use.engine.events.length + 1))[
          ordinal - (source.root.use.engine.events.length + 1)]? = some (.returned (.filesystem query) reply) := by
        rw [List.getElem?_drop]
        simpa only [Nat.add_sub_of_le sinceBirth] using selected
      exact False.elim (segment.before_quiet _ (List.mem_of_getElem? inDropped) (.inl removing))
    · omega
  let offset := ordinal - segment.beforeRaw.length
  have selectedRaw : (segment.events.map Program.filesystemEvent)[offset]? = some (.returned (.filesystem query) reply) := by
    simpa only [full, List.getElem?_append_right afterBefore, offset] using atEvent
  rw [List.getElem?_map] at selectedRaw
  cases selectedPair : segment.events[offset]? with
  | none => simp only [selectedPair, Option.map_none] at selectedRaw; cases selectedRaw
  | some pair =>
    simp only [selectedPair, Option.map_some, Option.some.injEq] at selectedRaw
    have decoded := congrArg PrimitiveFilesystem.filesystemEvent? selectedRaw
    have fields : (pair.1, some pair.2) = (query, some reply) := by
      change some (pair.1, some pair.2) = some (query, some reply) at decoded
      exact Option.some.inj decoded
    have first : pair.1 = query := congrArg Prod.fst fields
    have second : pair.2 = reply := Option.some.inj (congrArg Prod.snd fields)
    have samePair : pair = (query, reply) := Prod.ext first second
    subst pair
    obtain ⟨captured⟩ := segment.final_replies_private descriptors adapter guards eventTrace unlink opens privateRoot
      finalSource offset query reply selectedPair removing
    have count : segment.beforeRaw.length + offset = ordinal := Nat.add_sub_of_le afterBefore
    have capturedSource : SourceReturnAt runtime all actor ordinal Reply (.filesystem query) reply captured.before captured.after := by
      exact Eq.mp (congrArg (fun who => SourceReturnAt runtime all who ordinal Reply (.filesystem query) reply
        captured.before captured.after) sameActor) (count ▸ captured.sampled)
    have sameWorlds := same_ordinal_source_returns journal capturedSource sample
    exact ⟨captured.parent, sameWorlds.2.1 ▸ captured.live, captured.privateParent, captured.component⟩

end LeanCage.Host.Kernel
