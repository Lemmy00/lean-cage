import FilesystemReadSources.Handles

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.acceptance: A lost call is terminal; preceding source calls returned.
theorem prefix_prior_replies {α : Type} {program : Filesystem.Program α}
    {before : List (Request × Option Reply)} {event : Request × Option Reply}
    (source : Prefix program (before ++ [event])) :
    ∃ events, before = Publication.completed events := by
  induction before generalizing program with
  | nil => exact ⟨[], rfl⟩
  | cons first rest ih =>
    cases rest with
    | nil =>
      change Prefix program [first, event] at source
      cases source with
      | returned request next reply events tail =>
        exact ⟨[(request, reply)], rfl⟩
    | cons second rest =>
      change Prefix program (first :: second :: (rest ++ [event])) at source
      cases source with
      | returned request next reply events tail =>
        obtain ⟨following, shape⟩ := ih tail
        exact ⟨(request, reply) :: following, by
          simpa only [Publication.completed, List.map_cons] using congrArg ((request, some reply) :: ·) shape⟩

theorem prefix_before_last {α : Type} {program : Filesystem.Program α}
    {before : List (Request × Option Reply)} {event : Request × Option Reply}
    (source : Prefix program (before ++ [event])) : Prefix program before := by
  induction before generalizing program with
  | nil => exact .empty _
  | cons first rest ih =>
    cases rest with
    | nil =>
      change Prefix program [first, event] at source
      cases source with
      | returned request next reply events tail => exact .returned request next reply [] (.empty _)
    | cons second rest =>
      change Prefix program (first :: second :: (rest ++ [event])) at source
      cases source with
      | returned request next reply events tail => exact .returned request next reply _ (ih tail)

-- §FS-host-boundary.acceptance: Reconstruct the source prefix from its exact physical replies.
theorem physical_prefix_from_history {kernel : Contract} {α : Type} {program : Filesystem.Program α}
    {before after : World} {events : List (Request × Reply)}
    (history : History kernel before events after)
    (source : Prefix program (Publication.completed events)) :
    PhysicalPrefix kernel program before (Publication.completed events) after := by
  induction history generalizing program with
  | nil => exact .stop _ _
  | environment interference tail ih => exact .environment interference (ih source)
  | cons operation tail ih =>
    cases source with
    | returned request next reply events following => exact .returned operation (ih following)

theorem guarded_start_recorded {kernel : Contract} (laws : DescriptorContract kernel)
    (origin : FilesystemOrigin) (ordinal : Nat) {fd : UInt64} (start : GuardedCopyStart fd)
    {before after : World} (history : RecordedHistory kernel origin ordinal before start.events after) :
    Nonempty (GuardedHandle kernel origin (ordinal + start.events.length) after fd) := by
  cases start with
  | path path fd opening opened =>
    exact source_path_guard_recorded laws origin ordinal _ _ ⟨opened, history⟩
  | child parent name fd opening opened reply information parsed regular linked =>
    obtain ⟨middle, initial, rest⟩ := recorded_history_split opening _ history
    obtain ⟨guarded⟩ := source_open_guard_recorded laws origin ordinal _ _ _ ⟨opened, initial⟩
    obtain ⟨actual, final, leading, operation, sampled, trailing⟩ := recorded_history_head rest
    have actualLive : actual.handles fd = some guarded.handle := by
      rw [empty_recorded_handles leading]
      exact guarded.live
    have finalLive : final.handles fd = some guarded.handle := by
      rw [laws.retained _ _ _ _ operation (by simp [RetainsDescriptors])]
      exact actualLive
    have afterLive : after.handles fd = some guarded.handle := by
      rw [empty_recorded_handles trailing]
      exact finalLive
    refine ⟨⟨guarded.handle, afterLive, guarded.guard, ?_⟩⟩
    have earlier := guarded.earlier
    simp only [GuardedCopyStart.events, List.length_append, List.length_singleton]
    omega

structure SelectedGuardedRead {kernel : Contract} (runtime : ActorRuntime kernel)
    (ticks : List (ActorTick runtime)) (actor : ActorId) (position : Nat) (engine : EngineState)
    (request : Request) where
  handle : Handle
  live : engine.references request.first = some handle
  guard : PublicGuard kernel (fun ordinal request reply =>
    SourceReturnAt runtime ticks actor ordinal Reply (.filesystem request) reply) request.first handle
  guardPosition : Nat
  guardTick : ActorTick runtime
  selected : ticks[guardPosition]? = some guardTick
  action : guardTick.action = .returned actor (.filesystem {
    op := .getAttribute
    first := request.first
    second := 1
    left := PrivateNames.attributeName }) guard.reply
  earlier : guardPosition < position

-- §FS-host-boundary.snapshot: This selected read still uses its own earlier guarded raw object.
theorem actual_guarded_copy_read {kernel : Contract} {runtime : ActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (environment : InterferenceContract kernel)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply}
    (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    {context : List Program.Event} {before : List (Request × Option Reply)}
    (source : GuardedCopyCall before request observed)
    (trace : engine.events = context ++ before.map Program.filesystemPrefixEvent) (reading : request.op = .read) :
    Nonempty (SelectedGuardedRead runtime ticks actor position engine request) := by
  obtain ⟨actorHistory⟩ := actual_selected_actor_history descriptors lifetimes references environment
    journal selected action present
  obtain ⟨inside, insideShape⟩ := prefix_prior_replies source.active
  have history := actorHistory.history
  rw [trace, source.trace, insideShape] at history
  simp only [List.map_append, completed_filesystem_events, List.append_assoc] at history
  let earlier := context ++ source.context.map Program.filesystemPrefixEvent
  have phase : ActorHistoryWith runtime actor (SourceReturnAt runtime ticks actor) 0
      (actorHistory.launch.tick.after.project
        (.initial actorHistory.launch.references actorHistory.launch.closeExec actorHistory.launch.workingDirectory))
      (earlier ++ source.start.events.map Program.filesystemEvent ++ inside.map Program.filesystemEvent)
      (tick.before.project engine) := by
    simpa only [earlier, List.append_assoc, EngineState.initial] using history
  rw [List.append_assoc] at phase
  obtain ⟨first, leading, rest⟩ := actor_with_split earlier _ phase
  obtain ⟨copyBefore, opening, copying⟩ := actor_with_split (source.start.events.map Program.filesystemEvent) _ rest
  have recorded := actor_recorded_filesystem opening
  obtain ⟨guarded⟩ := guarded_start_recorded descriptors _ earlier.length source.start
    (by simpa only [Nat.zero_add] using recorded)
  have sourcePrefix := prefix_before_last source.active
  rw [insideShape] at sourcePrefix
  have copiedHistory := actor_recorded_filesystem copying
  have copiedPhysical := physical_prefix_from_history (recorded_history_erase copiedHistory) sourcePrefix
  have live := borrow_prefix (copyOpened_borrow descriptors source.fd guarded.handle source.fd source.limit)
    copiedPhysical guarded.live
  have requestFd := guarded_copy_call_descriptor source reading
  have requestLive : engine.references request.first = some guarded.handle := by
    rw [requestFd]
    exact live
  obtain ⟨guardPosition, guardTick, guardEngine, nextEngine, guardAt, guardAction, guardPresent,
    afterPresent, count, beforeShape, afterShape⟩ := guarded.guard.sampled
  have earlierSource : guardEngine.events.length < engine.events.length := by
    have bounded := guarded.earlier
    rw [trace, source.trace, insideShape]
    simp only [List.length_append, List.length_map, Publication.completed, earlier] at bounded count ⊢
    omega
  let sameGuard : PublicGuard kernel (fun ordinal request reply =>
      SourceReturnAt runtime ticks actor ordinal Reply (.filesystem request) reply) request.first guarded.handle := {
    ordinal := guarded.guard.ordinal
    before := guarded.guard.before
    after := guarded.guard.after
    reply := guarded.guard.reply
    actual := by simpa only [requestFd] using guarded.guard.actual
    sampled := by simpa only [requestFd] using guarded.guard.sampled
    live := by simpa only [requestFd] using guarded.guard.live
    accepted := guarded.guard.accepted
    absent := guarded.guard.absent }
  refine ⟨⟨guarded.handle, requestLive, sameGuard, guardPosition, guardTick, guardAt, ?_,
    source_ordinal_orders_positions journal guardAt selected actor guardEngine engine guardPresent present earlierSource⟩⟩
  simpa only [sameGuard, requestFd] using guardAction

-- §FS-host-boundary.snapshot: The maintained freeze caller supplies the guard producer itself.
theorem actual_snapshot_guarded_read {kernel : Contract} {runtime : ActorRuntime kernel}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (environment : InterferenceContract kernel)
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply}
    (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (workspace : Option ByteArray) (stdin : Snapshot.Stdin) (limits : Snapshot.Limits)
    {context : List Program.Event} {before : List (Request × Option Reply)}
    (source : Prefix (Snapshot.freeze workspace stdin limits) (before ++ [(request, observed)]))
    (trace : engine.events = context ++ before.map Program.filesystemPrefixEvent) (reading : request.op = .read) :
    Nonempty (SelectedGuardedRead runtime ticks actor position engine request) := by
  obtain ⟨guarded⟩ := freeze_read_sources workspace stdin limits _ _ _ source reading
  exact actual_guarded_copy_read descriptors lifetimes references environment journal selected action present
    guarded trace reading

-- §FS-host-boundary.publication: Key exclusion uses the same historical guard's physical object.
theorem selected_guarded_read_excludes {kernel : Contract} {runtime : ActorRuntime kernel}
    {ticks : List (ActorTick runtime)} {actor : ActorId} {position : Nat} {engine : EngineState}
    {request : Request} (source : SelectedGuardedRead runtime ticks actor position engine request)
    {key : ObjectId} {value : ByteArray}
    (marked : source.guard.before.attributes key PrivateNames.attributeName = some value) :
    source.handle.object ≠ key := by
  intro same
  have absent := source.guard.absent
  rw [same, marked] at absent
  cases absent

end LeanCage.Host.Kernel
