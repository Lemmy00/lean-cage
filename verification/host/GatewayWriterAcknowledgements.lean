import GatewayStreamWriter

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

variable {kernel : Contract} {sourceProgram : Program UInt32}
  {runtime : ActorRuntime kernel sourceProgram}

-- §AR-host-boundary.interfaces.gateway: The actor's actual reply/loss row
-- advances its event ordinal once. Unrelated rows append no source event.
theorem actor_step_exact_events {action : ActorAction} {before after : Population}
    (step : ActorStep runtime action before after)
    (query : ActorId) (initial : EngineState) (present : before.actors query = some initial) :
    ∃ final, after.actors query = some final ∧
      final.events = initial.events ++ (action.eventFor query).toList := by
  cases step with
  | @launch population actor references closeExec workingDirectory fresh absent inherited =>
    have different : query ≠ actor := by
      intro same
      subst query
      rw [absent] at present
      cases present
    exact ⟨initial, by simpa only [Population.launch, Population.install, ite_eq_right different] using present,
      by simp [ActorAction.eventFor]⟩
  | @returned β population actor engine effect next reply world current alive head actual =>
    by_cases same : query = actor
    · subst actor
      have sameEngine := Option.some.inj (present.symm.trans current)
      subst engine
      refine ⟨initial.returned effect reply next world, ?_, ?_⟩
      · simp [Population.advance, Population.install]
      · simp [EngineState.returned, ActorAction.eventFor]
    · exact ⟨initial,
        by simpa only [Population.advance, Population.install, ite_eq_right same] using present,
        by simp [ActorAction.eventFor, same]⟩
  | @lost β population actor engine effect next world current alive head actual =>
    by_cases same : query = actor
    · subst actor
      have sameEngine := Option.some.inj (present.symm.trans current)
      subst engine
      refine ⟨initial.lost effect world, ?_, ?_⟩
      · simp [Population.advance, Population.install]
      · simp [EngineState.lost, ActorAction.eventFor]
    · exact ⟨initial,
        by simpa only [Population.advance, Population.install, ite_eq_right same] using present,
        by simp [ActorAction.eventFor, same]⟩
  | foreign actual => exact ⟨initial, present, by simp [ActorAction.eventFor]⟩
  | @retire population actor engine observation world current actual =>
    by_cases same : query = actor
    · subst actor
      have identity := Option.some.inj (present.symm.trans current)
      subst engine
      exact ⟨initial.retired observation world,
        by simp [Population.advance, Population.install], by simp [EngineState.retired, ActorAction.eventFor]⟩
    · exact ⟨initial,
        by simpa only [Population.advance, Population.install, ite_eq_right same] using present,
        by simp [ActorAction.eventFor]⟩
  | nativeRetire actual => exact ⟨initial, present, by simp [ActorAction.eventFor]⟩

variable {runtime : PrimitiveActorRuntime kernel} {ticks : List (ActorTick runtime)} {pair : Pair}

structure EngineWriteObservation (entry : EngineWriteEntry ticks pair) (reply : Option Reply) : Prop where
  action : entry.tick.action.eventFor entry.actor = some (Program.filesystemPrefixEvent (entry.request, reply))

-- §FS-host-boundary.caller: This derives the real post-ACK/loss source state.
-- It does not enqueue bytes, assert a successful count, or infer helper exit.
theorem engine_write_observation_ordinal (entry : EngineWriteEntry ticks pair) (reply : Option Reply)
    (observed : EngineWriteObservation entry reply) :
    ∃ after, entry.tick.after.actors entry.actor = some after ∧
      after.events = entry.engine.events ++ [Program.filesystemPrefixEvent (entry.request, reply)] ∧
      after.events.length = entry.engine.events.length + 1 := by
  obtain ⟨after, present, events⟩ := actor_step_exact_events entry.tick.operation entry.actor entry.engine entry.present
  rw [observed.action] at events
  have exactEvents : after.events = entry.engine.events ++ [Program.filesystemPrefixEvent (entry.request, reply)] := by
    simpa only [Option.toList_some] using events
  exact ⟨after, present, exactEvents, by simp only [exactEvents, List.length_append, List.length_singleton]⟩

theorem selected_tick_exact_split {position : Nat} {tick : ActorTick runtime}
    (selected : ticks[position]? = some tick) :
    ∃ leading trailing, leading.length = position ∧ ticks = leading ++ tick :: trailing := by
  induction position generalizing ticks with
  | zero =>
    cases ticks with
    | nil => cases selected
    | cons first rest =>
      have same := Option.some.inj selected
      subst first
      exact ⟨[], rest, rfl, rfl⟩
  | succ position ih =>
    cases ticks with
    | nil => cases selected
    | cons first rest =>
      obtain ⟨leading, trailing, count, shape⟩ := ih selected
      exact ⟨first :: leading, trailing, by simp only [List.length_cons, count], by rw [shape]; rfl⟩

-- §AR-host-boundary.primitives: A later pending chunk follows the actual ACK
-- ordinal even if the physical write was committed before its observation.
theorem later_writer_after_observation {before after : Population}
    (journal : ActorJournal runtime before ticks after)
    (first last : EngineWriteEntry ticks pair) (reply : Option Reply)
    (observed : EngineWriteObservation first reply)
    (actor : first.actor = last.actor) (ordered : first.position < last.position) :
    first.engine.events.length < last.engine.events.length := by
  obtain ⟨following, present, events, count⟩ := engine_write_observation_ordinal first reply observed
  have followingPrefix : following.events <+: last.engine.events := by
    obtain ⟨leading, rest, length, shape⟩ := selected_tick_exact_split first.selected
    rw [shape] at journal
    obtain ⟨middle, _, suffix⟩ := actor_journal_split leading _ journal
    cases suffix with
    | cons tail =>
      have atLast : rest[last.position - (first.position + 1)]? = some last.tick := by
        have selected : (leading ++ first.tick :: rest)[last.position]? = some last.tick :=
          (congrArg (fun items : List (ActorTick runtime) => items[last.position]?) shape).symm.trans last.selected
        have index : last.position - leading.length = (last.position - (first.position + 1)) + 1 := by omega
        rw [List.getElem?_append_right (by omega), index, List.getElem?_cons_succ] at selected
        exact selected
      obtain ⟨between, prefixRun⟩ := journal_to_selected tail atLast
      have earlier : first.tick.after.actors last.actor = some following := by simpa only [actor] using present
      obtain ⟨extra, shape⟩ := actor_journal_event_prefix prefixRun last.actor following last.engine earlier last.present
      exact ⟨extra, shape.symm⟩
  have bounded := List.IsPrefix.length_le followingPrefix
  omega

end LeanCage.Host.PrivateStreams
