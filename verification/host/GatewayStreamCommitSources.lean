import GatewayChannelWriteSources

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {ticks : List (ActorTick runtime)} {pair : Pair} {Token : Type}

-- §AR-host-boundary.interfaces.gateway: Select the real registered entry
-- of a partial commit and retain its exact final ledger, even after loss.
theorem ObservedJournal.engine_commit_source
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {position : Nat} {initial final : PhysicalState} {records : List Record}
    (journal : ObservedJournal primitive position initial records final)
    (registered : Registered primitive position initial)
    (record : Record) (member : record ∈ records) (actor ordinal extent : Nat)
    (event : record.event = .commit (.engine actor ordinal) extent) :
    ∃ entry token current, primitive.enteredEngine token entry ∧ entry.key = .engine actor ordinal ∧
      final.ledger entry.key = some current := by
  induction journal with
  | nil => cases member
  | @cons position initial middle final first rest order actual tail ih =>
    rcases List.mem_cons.mp member with same | later
    · subst record
      cases actual with
      | engine | native | read | birth | other => cases event
      | observation position inside token current state before after reply stored live observed =>
        cases reply <;> cases event
      | commit position inside token current state before after count stored live observed =>
        have key := (ProgressEvent.commit.inj event).1
        have selected : initial.ledger (.engine actor ordinal) = some current := by rw [← key]; exact stored
        obtain ⟨entry, sourceToken, entered, identity, input, earlier⟩ :=
          registered_engine_source registered actor ordinal current selected
        have nextSelected : (initial.ledger.set (primitive.input token).1
            {current with committed := count, bounded := (primitive.progressLaw _ _ _ _ _ _ observed).1.symm ▸
              (primitive.progressLaw _ _ _ _ _ _ observed).2.2.2.1}) entry.key =
            some {current with committed := count, bounded := (primitive.progressLaw _ _ _ _ _ _ observed).1.symm ▸
              (primitive.progressLaw _ _ _ _ _ _ observed).2.2.2.1} := by
          simp only [Ledger.set, identity, key, ite_true]
        obtain ⟨last, present, input, increased, bytes⟩ := tail.key_bytes entry.key _ nextSelected
        exact ⟨entry, sourceToken, last, entered, identity, present⟩
    · exact ih (actual.registered order registered) later

end LeanCage.Host.PrivateStreams
