import GatewayStreamExtents

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

-- §FS-host-boundary.caller: A source ordinal which has advanced past a
-- returned write cannot enqueue again. A lost final call is kept separate.
def OlderReturned (actor ordinal : Nat) (ledger : Ledger) : Prop :=
  ∀ older, older < ordinal → ∀ current, ledger (.engine actor older) = some current →
    ∃ reply, current.observation = .returned reply

theorem step_older_returned {initial final : PhysicalState} {record : Record}
    (actual : ProgressStep initial record.event record.actions final) (actor ordinal : Nat)
    (older : OlderReturned actor ordinal initial.ledger)
    (noOldEntry : ∀ key input, record.event = .begin (.engine actor key) input → ordinal ≤ key) :
    OlderReturned actor ordinal final.ledger := by
  intro selected bound current stored
  cases record with | mk position event actions =>
    cases actual with
    | begin added input fresh =>
      by_cases same : CallKey.engine actor selected = added
      · subst added
        have impossible := noOldEntry selected input rfl
        omega
      · exact older selected bound current (by simpa only [Ledger.set, ite_eq_right same] using stored)
    | commit added previous stream extent previousAt live unreturned increase bounded writable =>
      by_cases same : CallKey.engine actor selected = added
      · subst added
        obtain ⟨reply, returned⟩ := older selected bound previous previousAt
        simp only [WriteProgress.canCommit, returned] at unreturned
      · exact older selected bound current (by simpa only [Ledger.set, ite_eq_right same] using stored)
    | returned added previous reply previousAt pending count =>
      by_cases same : CallKey.engine actor selected = added
      · subst added
        obtain ⟨reply, returned⟩ := older selected bound previous previousAt
        rw [returned] at pending
        cases pending
      · exact older selected bound current (by simpa only [Ledger.set, ite_eq_right same] using stored)
    | lost added previous previousAt pending =>
      by_cases same : CallKey.engine actor selected = added
      · subst added
        obtain ⟨reply, returned⟩ := older selected bound previous previousAt
        rw [returned] at pending
        cases pending
      · exact older selected bound current (by simpa only [Ledger.set, ite_eq_right same] using stored)
    | channel => exact older selected bound current stored

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {ticks : List (ActorTick runtime)} {pair : Pair} {Token : Type}

theorem ObservedStep.engine_entry_ordinal
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {initial final : PhysicalState} {record : Record} (actual : ObservedStep primitive initial record final)
    (tick : ActorTick runtime) (selectedTick : ticks[record.position]? = some tick)
    (actor ordinal : Nat) (input : WriteDescription)
    (entry : record.event = .begin (.engine actor ordinal) input) :
    ∃ engine, tick.before.actors actor = some engine ∧ ordinal = engine.events.length := by
  cases actual with
  | engine state source token entered fresh =>
    have sameTick := Option.some.inj (source.selected.symm.trans selectedTick)
    have key := ProgressEvent.begin.inj entry
    have fields := CallKey.engine.inj key.1
    exact ⟨source.engine, by simpa only [← sameTick, ← fields.1] using source.present, fields.2.symm⟩
  | native => cases entry
  | commit => cases entry
  | observation position inside token current state initial final reply selected live actual =>
    cases reply <;> cases entry
  | read => cases entry
  | birth => cases entry
  | other => cases entry

theorem ObservedJournal.older_returned
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {position : Nat} {initial final : PhysicalState} {records : List Record}
    (journal : ObservedJournal primitive position initial records final) (actor ordinal : Nat)
    (before : OlderReturned actor ordinal initial.ledger)
    (births : ∀ record ∈ records, ∀ key input,
      record.event = .begin (.engine actor key) input → ordinal ≤ key) :
    OlderReturned actor ordinal final.ledger := by
  induction journal with
  | nil => exact before
  | cons order actual tail ih =>
    apply ih (step_older_returned actual.erase actor ordinal before (births _ (by simp)))
    intro record member
    exact births record (by simp [member])

-- §AR-host-boundary.interfaces.gateway: New ledger entries at this actual
-- global row use the actor's real current ordinal. They cannot resurrect an
-- earlier source call after its ACK, even if descriptor numbers are reused.
theorem PendingBatch.older_returned
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {position : Nat} {initial final : PhysicalState} {records : List Record}
    (batch : PendingBatch primitive position initial final records)
    (tick : ActorTick runtime) (selectedTick : ticks[position]? = some tick)
    (actor : ActorId) (engine : EngineState) (present : tick.before.actors actor = some engine)
    (before : OlderReturned actor engine.events.length initial.ledger) :
    OlderReturned actor engine.events.length final.ledger := by
  apply batch.actual.older_returned actor engine.events.length before
  intro record member ordinal input event
  have selected : ticks[record.position]? = some tick := by rw [batch.positions record member]; exact selectedTick
  have noOldBirth : ∀ {first last : PhysicalState},
      ObservedStep primitive first record last → engine.events.length ≤ ordinal := by
    intro first last actual
    obtain ⟨original, source, count⟩ := actual.engine_entry_ordinal tick selected actor ordinal input event
    have same := Option.some.inj (source.symm.trans present)
    subst original
    omega
  have occurs : ∃ first last, Nonempty (ObservedStep primitive first record last) := by
    have history := batch.actual
    clear before batch selectedTick present event selected noOldBirth
    induction history with
    | nil => cases member
    | cons order actual tail ih =>
      rcases List.mem_cons.mp member with same | later
      · subst record; exact ⟨_, _, ⟨actual⟩⟩
      · exact ih later
  obtain ⟨first, last, ⟨actual⟩⟩ := occurs
  exact noOldBirth actual

end LeanCage.Host.PrivateStreams
