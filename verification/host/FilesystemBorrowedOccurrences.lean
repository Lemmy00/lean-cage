import FilesystemUses
import FilesystemSourceNondestructive
import FilesystemPrimitiveIntervals

namespace LeanCage.Host.Kernel
open Filesystem

private theorem recorded_selected_origin {kernel : Contract} {origin : FilesystemOrigin} {ordinal : Nat}
    {before after : World} {events : List (Request × Reply)}
    (history : RecordedHistory kernel origin ordinal before events after)
    {offset : Nat} {request : Request} {reply : Reply} (selected : events[offset]? = some (request, reply)) :
    ∃ first last, kernel.step first request (some reply) last ∧ origin (ordinal + offset) request reply first last := by
  induction history generalizing offset with
  | nil => cases selected
  | environment actual tail ih => exact ih selected
  | cons actual sampled tail ih =>
    cases offset with
    | zero => cases selected; exact ⟨_, _, actual, by simpa only [Nat.add_zero] using sampled⟩
    | succ offset =>
      obtain ⟨first, last, actual, sampled⟩ := ih selected
      exact ⟨first, last, actual, by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using sampled⟩

-- §FS-host-boundary.ownership: Each needed use gets the actual captured input
-- of this source occurrence. Release may follow the last use; FD reuse,
-- arbitrary intervening replies and unrelated world effects remain possible.
theorem borrowed_recorded_use_at {kernel : Contract} {origin : FilesystemOrigin} {ordinal : Nat}
    {held : UInt64} {handle : Handle} {needs : Request → Prop}
    {α : Type} {program : Filesystem.Program α}
    (source : BorrowUses kernel held handle needs program)
    {before after : World} {events : List (Request × Reply)}
    (active : Prefix program (Publication.completed events)) (history : RecordedHistory kernel origin ordinal before events after)
    (live : before.handles held = some handle)
    {offset : Nat} {request : Request} {reply : Reply} (selected : events[offset]? = some (request, reply)) :
    ∃ first last, kernel.step first request (some reply) last ∧
      origin (ordinal + offset) request reply first last ∧ (needs request → first.handles held = some handle) := by
  induction history generalizing program offset with
  | nil => cases selected
  | environment actual tail ih =>
    apply ih source active ?_ selected
    rw [kernel.interference_handles _ _ actual]
    exact live
  | @cons ordinal before middle after operation answer events actual sampled tail ih =>
    change Prefix program ((operation, some answer) :: Publication.completed events) at active
    cases active with
    | returned _ next _ _ following =>
      cases source with
      | unused allowed =>
        obtain ⟨first, last, occurrence, captured⟩ := recorded_selected_origin (.cons actual sampled tail) selected
        have occurs : (request, some reply) ∈ Publication.completed ((operation, answer) :: events) :=
          List.mem_map.mpr ⟨(request, reply), List.mem_of_getElem? selected, rfl⟩
        have notNeeded := request_prefix allowed (Prefix.returned operation next answer _ following)
          (request, some reply) occurs
        exact ⟨first, last, occurrence, captured, fun needed => False.elim (notNeeded needed)⟩
      | call preserve continuation =>
        cases offset with
        | zero =>
          cases selected
          exact ⟨before, middle, actual, by simpa only [Nat.add_zero] using sampled, fun _ => live⟩
        | succ offset =>
          obtain ⟨first, last, occurrence, captured, reference⟩ :=
            ih (continuation _ _ _ actual live) following (preserve _ _ _ actual live) selected
          exact ⟨first, last, occurrence,
            by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using captured, reference⟩

-- §AR-host-boundary.primitives: Distinct completed calls of one source actor
-- have strictly ordered source ordinals. Equal integer descriptors/arguments
-- cannot match a second global occurrence to an earlier captured resource.
theorem returned_positions_order_source_ordinals {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {before after : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime before all after)
    {first second : Nat} {left right : ActorTick runtime}
    (leftAt : all[first]? = some left) (rightAt : all[second]? = some right) (ordered : first < second)
    {actor : ActorId} {initial final : EngineState} {β : Type} {effect : Effect β} {reply : β}
    (action : left.action = .returned actor effect reply)
    (present : left.before.actors actor = some initial) (later : right.before.actors actor = some final) :
    initial.events.length < final.events.length := by
  have event : left.action.eventFor actor = some (.returned effect reply) := by
    simp only [action, ActorAction.eventFor, ↓reduceIte]
  obtain ⟨middle, middlePresent, trace⟩ := source_event_after left event present
  obtain ⟨leading, inside, trailing, shape, count, interval⟩ := journal_between_after journal leftAt rightAt ordered
  obtain ⟨extra, extended⟩ := actor_journal_event_prefix interval actor middle final middlePresent later
  have length := congrArg List.length (extended.trans (congrArg (· ++ extra) trace))
  simp only [List.length_append, List.length_singleton] at length
  omega

theorem same_ordinal_source_returns {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {before after : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime before all after)
    {actor ordinal : Nat} {request firstRequest : Request} {reply firstReply : Reply}
    {firstBefore firstAfter secondBefore secondAfter : World}
    (first : SourceReturnAt runtime all actor ordinal Reply (.filesystem firstRequest) firstReply firstBefore firstAfter)
    (second : SourceReturnAt runtime all actor ordinal Reply (.filesystem request) reply secondBefore secondAfter) :
    firstRequest = request ∧ firstBefore = secondBefore ∧ firstAfter = secondAfter := by
  obtain ⟨firstPosition, firstTick, input, output, firstAt, firstAction, present, afterPresent,
    firstCount, beforeWorld, afterWorld⟩ := first
  obtain ⟨secondPosition, secondTick, nextInput, nextOutput, secondAt, secondAction, nextPresent, nextAfterPresent,
    secondCount, nextBeforeWorld, nextAfterWorld⟩ := second
  have position : firstPosition = secondPosition := by
    rcases Nat.lt_trichotomy firstPosition secondPosition with earlier | same | later
    · have count := returned_positions_order_source_ordinals journal firstAt secondAt earlier firstAction present nextPresent
      omega
    · exact same
    · have count := returned_positions_order_source_ordinals journal secondAt firstAt later secondAction nextPresent present
      omega
  have tick : firstTick = secondTick := Option.some.inj (firstAt.symm.trans (position.symm ▸ secondAt))
  subst secondTick
  have sameInput : input = nextInput := Option.some.inj (present.symm.trans nextPresent)
  have sameOutput : output = nextOutput := Option.some.inj (afterPresent.symm.trans nextAfterPresent)
  have actions := firstAction.symm.trans secondAction
  have event := congrArg (fun action => action.eventFor actor) actions
  simp only [ActorAction.eventFor, ↓reduceIte, Option.some.injEq] at event
  have decoded := congrArg PrimitiveFilesystem.filesystemEvent? event
  have pair : (firstRequest, some firstReply) = (request, some reply) := by
    change some (firstRequest, some firstReply) = some (request, some reply) at decoded
    exact Option.some.inj decoded
  exact ⟨congrArg Prod.fst pair,
    beforeWorld.trans ((congrArg (fun engine => firstTick.before.project engine) sameInput).trans nextBeforeWorld.symm),
    afterWorld.trans ((congrArg (fun engine => firstTick.after.project engine) sameOutput).trans nextAfterWorld.symm)⟩

theorem filesystem_event_returned_action {action : ActorAction} {actor : ActorId} {request : Request} {reply : Reply}
    (source : action.eventFor actor = some (.returned (.filesystem request) reply)) :
    action = .returned actor (.filesystem request) reply := by
  cases action with
  | returned who effect answer =>
    by_cases same : actor = who
    · subst who
      simp only [ActorAction.eventFor, ↓reduceIte, Option.some.injEq] at source
      cases source
      rfl
    · simp only [ActorAction.eventFor, ite_eq_right same] at source
      cases source
  | launch | foreign | retire | nativeRetire => cases source
  | lost who effect =>
    by_cases same : actor = who
    · subst who
      simp only [ActorAction.eventFor, ↓reduceIte, Option.some.injEq] at source
      cases source
    · simp only [ActorAction.eventFor, ite_eq_right same] at source
      cases source

-- §FS-host-boundary.ownership: A real earlier source call occupies its actual
-- ordinal in this later actor transcript. Interleaving steps do not change
-- the event, its order, or its one-call position.
theorem prior_source_event_index {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {before after : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime before all after)
    {first second : Nat} {left right : ActorTick runtime}
    (leftAt : all[first]? = some left) (rightAt : all[second]? = some right) (ordered : first < second)
    {actor : ActorId} {initial final : EngineState} {event : Program.Event}
    (action : left.action.eventFor actor = some event)
    (present : left.before.actors actor = some initial) (later : right.before.actors actor = some final) :
    final.events[initial.events.length]? = some event := by
  obtain ⟨middle, middlePresent, trace⟩ := source_event_after left action present
  obtain ⟨leading, inside, trailing, shape, count, interval⟩ := journal_between_after journal leftAt rightAt ordered
  obtain ⟨extra, extended⟩ := actor_journal_event_prefix interval actor middle final middlePresent later
  have full : final.events = initial.events ++ event :: extra := by
    rw [extended, trace]
    simp only [List.append_assoc, List.singleton_append]
  rw [full, List.getElem?_append_right (by omega), Nat.sub_self]
  rfl

theorem actor_history_excludes_lost {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {actor : ActorId} {origin : OperationOrigin}
    {ordinal : Nat} {before after : World} {events : List Program.Event}
    (history : ActorHistoryWith runtime actor origin ordinal before events after)
    {β : Type} (effect : Effect β) : .lost effect ∉ events := by
  induction history with
  | nil => simp
  | returned actual sampled tail ih =>
    intro member
    rcases List.mem_cons.mp member with same | member
    · cases same
    · exact ih member
  | environment actual tail ih => exact ih

theorem selected_source_return {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {all : List (ActorTick runtime)}
    {position : Nat} {tick : ActorTick runtime} (selected : all[position]? = some tick)
    {actor : ActorId} {engine : EngineState} (present : tick.before.actors actor = some engine)
    {request : Request} {reply : Reply} (action : tick.action = .returned actor (.filesystem request) reply) :
    ∃ output, SourceReturnAt runtime all actor engine.events.length Reply (.filesystem request) reply
      (tick.before.project engine) (tick.after.project output) := by
  have event : tick.action.eventFor actor = some (.returned (.filesystem request) reply) := by
    simp only [action, ActorAction.eventFor, ↓reduceIte]
  obtain ⟨output, outputPresent, appended⟩ := source_event_after tick event present
  exact ⟨output, position, tick, engine, output, selected, action, present, outputPresent, rfl, rfl, rfl⟩

end LeanCage.Host.Kernel
