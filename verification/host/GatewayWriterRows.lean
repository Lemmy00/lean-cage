import GatewayWriterReconciliation

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

structure WriteObservation where
  actor : ActorId
  ordinal : Nat
  request : Request
  reply : Option Reply

private def writeObservationFor {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (tick : ActorTick runtime) (actor : ActorId) (request : Request) (reply : Option Reply) : Option WriteObservation :=
  if request.op = .write then
    match tick.before.actors actor with
    | none => none
    | some engine => some ⟨actor, engine.events.length, request, reply⟩
  else none

-- §AR-host-boundary.interfaces.gateway: Read EVERY actual write reply/loss
-- row from the stored action. A role label cannot silently omit one of them.
def writeObservationAt {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    (tick : ActorTick runtime) : Option WriteObservation :=
  match tick.action with
  | .returned actor (.filesystem request) reply => writeObservationFor tick actor request (some reply)
  | .lost actor (.filesystem request) => writeObservationFor tick actor request none
  | _ => none

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {ticks : List (ActorTick runtime)} {pair : Pair}

theorem write_observation_complete (tick : ActorTick runtime) (actor : ActorId) (engine : EngineState)
    (present : tick.before.actors actor = some engine) (request : Request) (reply : Option Reply)
    (writing : request.op = .write)
    (observed : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, reply))) :
    writeObservationAt tick = some ⟨actor, engine.events.length, request, reply⟩ := by
  cases operation : tick.action with
  | returned who effect response =>
    by_cases same : actor = who
    · subst who
      cases reply with
      | none => simp [operation, ActorAction.eventFor, Program.filesystemPrefixEvent] at observed
      | some reply =>
        simp only [operation, ActorAction.eventFor, ite_true, Program.filesystemPrefixEvent,
          Option.some.injEq] at observed
        cases observed
        simp only [writeObservationAt, operation, writeObservationFor, writing, ↓reduceIte, present]
    · simp [operation, ActorAction.eventFor, same] at observed
  | lost who effect =>
    by_cases same : actor = who
    · subst who
      cases reply with
      | some reply => simp [operation, ActorAction.eventFor, Program.filesystemPrefixEvent] at observed
      | none =>
        simp only [operation, ActorAction.eventFor, ite_true, Program.filesystemPrefixEvent,
          Option.some.injEq] at observed
        cases observed
        simp only [writeObservationAt, operation, writeObservationFor, writing, ↓reduceIte, present]
    · simp [operation, ActorAction.eventFor, same] at observed
  | launch | foreign | retire | nativeRetire => simp [operation, ActorAction.eventFor] at observed

theorem write_observation_fields (tick : ActorTick runtime) (actual : WriteObservation)
    (selected : writeObservationAt tick = some actual) :
    ∃ engine, tick.before.actors actual.actor = some engine ∧ engine.events.length = actual.ordinal ∧
      actual.request.op = .write ∧ tick.action.eventFor actual.actor =
        some (Program.filesystemPrefixEvent (actual.request, actual.reply)) := by
  cases operation : tick.action with
  | returned actor effect reply =>
    cases effect <;> simp only [writeObservationAt, operation] at selected
    case filesystem request =>
      unfold writeObservationFor at selected
      split at selected
      next writing =>
        cases present : tick.before.actors actor with
        | none => simp only [present] at selected; cases selected
        | some engine =>
          simp only [present, Option.some.injEq] at selected
          subst actual
          exact ⟨engine, present, rfl, writing, by simp [ActorAction.eventFor, Program.filesystemPrefixEvent]⟩
      next => cases selected
    all_goals cases selected
  | lost actor effect =>
    cases effect <;> simp only [writeObservationAt, operation] at selected
    case filesystem request =>
      unfold writeObservationFor at selected
      split at selected
      next writing =>
        cases present : tick.before.actors actor with
        | none => simp only [present] at selected; cases selected
        | some engine =>
          simp only [present, Option.some.injEq] at selected
          subst actual
          exact ⟨engine, present, rfl, writing, by simp [ActorAction.eventFor, Program.filesystemPrefixEvent]⟩
      next => cases selected
    all_goals cases selected
  | launch | foreign | retire | nativeRetire => simp only [writeObservationAt, operation] at selected; cases selected

-- §FS-host-boundary.caller: The observed source key is computed from the real
-- actor/ordinal. Physical synchronization must reconcile this selected key.
def WriteObservation.key (observation : WriteObservation) : CallKey :=
  .engine observation.actor observation.ordinal

end LeanCage.Host.PrivateStreams
