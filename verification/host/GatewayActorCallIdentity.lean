import GatewayWriterAcknowledgements

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem
universe u

-- §AR-host-boundary.interfaces.gateway: A raw actor ordinal identifies its
-- actual dependent source call, including the exact byte/path arguments.
theorem residual_current_unique {α : Type} {program first last : Program α} {events : List Program.Event}
    (before : Residual program events first) (after : Residual program events last) : first = last := by
  induction before generalizing last with
  | refl => cases after; rfl
  | call tail ih => cases after with | call rest => exact ih rest

private theorem prefix_length_equal {α : Type u} {first last : List α}
    (leading : first <+: last) (count : first.length = last.length) : first = last := by
  obtain ⟨rest, rfl⟩ := leading
  cases rest with
  | nil => simp
  | cons head tail => simp only [List.length_append, List.length_cons] at count; omega

def filesystemHead {α : Type} : Program α → Option Request
  | .pure _ => none
  | .call effect _ => match effect with | .filesystem request => some request | _ => none

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {ticks : List (ActorTick runtime)} {pair : Pair}

theorem actual_filesystem_observation_head {action : ActorAction} {before after : Population}
    (actual : ActorStep runtime action before after) (actor : ActorId) (request : Request) (reply : Option Reply)
    (observed : action.eventFor actor = some (Program.filesystemPrefixEvent (request, reply))) :
    ∃ engine next, before.actors actor = some engine ∧ engine.running = true ∧
      engine.current = .call (.filesystem request) next := by
  cases actual with
  | launch => simp [ActorAction.eventFor] at observed
  | @returned β population who engine effect next response world present alive head operation =>
    by_cases same : actor = who
    · subst actor
      cases reply with
      | none => simp [ActorAction.eventFor, Program.filesystemPrefixEvent] at observed
      | some reply =>
        simp only [ActorAction.eventFor, ite_true, Program.filesystemPrefixEvent, Option.some.injEq] at observed
        cases observed
        exact ⟨engine, next, present, alive, head⟩
    · simp [ActorAction.eventFor, same] at observed
  | @lost β population who engine effect next world present alive head operation =>
    by_cases same : actor = who
    · subst actor
      cases reply with
      | some reply => simp [ActorAction.eventFor, Program.filesystemPrefixEvent] at observed
      | none =>
        simp only [ActorAction.eventFor, ite_true, Program.filesystemPrefixEvent, Option.some.injEq] at observed
        cases observed
        exact ⟨engine, next, present, alive, head⟩
    · simp [ActorAction.eventFor, same] at observed
  | foreign | retire | nativeRetire => simp [ActorAction.eventFor] at observed

theorem actual_same_ordinal_request {initial : World} {final : Population}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    (entry : EngineWriteEntry ticks pair) {position : Nat} {tick : ActorTick runtime}
    (selected : ticks[position]? = some tick) (engine : EngineState)
    (present : tick.before.actors entry.actor = some engine) (running : engine.running = true)
    (ordinal : engine.events.length = entry.engine.events.length)
    (request : Request) (next : Reply → Program UInt32)
    (head : engine.current = .call (.filesystem request) next) : request = entry.request := by
  have events : engine.events = entry.engine.events := by
    rcases Nat.le_total entry.position position with ordered | ordered
    · exact (prefix_length_equal
        (selected_events_prefix journal ordered entry.selected selected entry.actor entry.engine engine
          entry.present present) ordinal.symm).symm
    · exact prefix_length_equal
        (selected_events_prefix journal ordered selected entry.selected entry.actor engine entry.engine
          present entry.present) ordinal
  obtain ⟨firstLeading, firstTrailing, _, firstShape⟩ := selected_tick_exact_split entry.selected
  obtain ⟨lastLeading, lastTrailing, _, lastShape⟩ := selected_tick_exact_split selected
  have before := selected_actor_head_for journal firstLeading firstTrailing entry.tick firstShape entry.present entry.running
  have after := selected_actor_head_for journal lastLeading lastTrailing tick lastShape present running
  rw [events] at after
  have current := residual_current_unique after before
  rw [head, entry.head] at current
  exact Option.some.inj (congrArg filesystemHead current)

end LeanCage.Host.PrivateStreams
