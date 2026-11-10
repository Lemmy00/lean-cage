import FilesystemCleanupStageSegment

namespace LeanCage.Host.Kernel
open Filesystem
universe u

private theorem drop_append_allowed {α : Type u} {first last : List α} (count : Nat) (allowed : α → Prop)
    (leading : ∀ event ∈ first.drop count, allowed event) (trailing : ∀ event ∈ last, allowed event) :
    ∀ event ∈ (first ++ last).drop count, allowed event := by
  intro event member
  rw [List.drop_append] at member
  rcases List.mem_append.mp member with member | member
  · exact leading event member
  · exact trailing event (List.mem_of_mem_drop member)

-- §FS-host-boundary.ownership: Between the actual private birth and cleanup
-- entry, real reopen/stat/preparation calls contain no removal or rename.
-- This source fact includes guard rejection closes and failed preparation.
theorem CleanupStageSegment.before_quiet {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {initial : World} {all : List (ActorTick runtime)} {before : List Program.Event} {request : Request}
    {call : PublicationCleanup.Host before request} {limit : Nat} {current : World}
    {source : CleanupStageContinuation runtime initial all call limit current}
    (segment : CleanupStageSegment source) :
    ∀ event ∈ segment.beforeRaw.drop (source.root.use.engine.events.length + 1), NondestructiveEvent event := by
  apply Eq.mpr (congrArg (fun actualEvents : List Program.Event =>
    ∀ event ∈ actualEvents.drop (source.root.use.engine.events.length + 1), NondestructiveEvent event)
    segment.beforeTrace)
  apply drop_append_allowed
  · intro event member
    exact passive_event_nondestructive (source.root.probes event member)
  · intro event member
    rcases List.mem_cons.mp member with rfl | member
    · simp only [NondestructiveEvent, DestructiveRequest, source.opening.opening]
      decide
    · rcases List.mem_append.mp member with member | preparing
      · rcases List.mem_append.mp member with postMember | inspected
        · obtain ⟨⟨query, reply⟩, occurs, rfl⟩ := List.mem_map.mp postMember
          exact namespace_passive_not_destructive (source.earlier.passive (query, reply) occurs)
        · rw [source.inspection] at inspected
          have same : event = .returned (.filesystem {
              op := .stat, first := call.source.attempt.context.stage.directory.fd}) source.informationReply := by
            simpa only [List.map_cons, List.map_nil, List.mem_singleton, Program.filesystemEvent] using inspected
          subst event
          simp [NondestructiveEvent, DestructiveRequest]
      · obtain ⟨events, prepared, trace⟩ :=
          PrimitiveFilesystem.chunks_filesystem_returns call.source.attempt.prepared segment.preparingChunks
        rw [trace] at preparing
        obtain ⟨pair, occurs, rfl⟩ := List.mem_map.mp preparing
        exact requests_returned (lower_nondestructive (publication_prepare_nondestructive _ _ _ _ _ _ _)) prepared pair occurs

end LeanCage.Host.Kernel
