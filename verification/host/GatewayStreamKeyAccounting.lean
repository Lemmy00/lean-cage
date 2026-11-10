import GatewayStreamExtents

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

theorem step_unregistered_key {initial final : PhysicalState} {record : Record}
    (actual : ProgressStep initial record.event record.actions final) (key : CallKey)
    (absent : initial.ledger key = none) :
    record.bytesFor key = [] ∧
      (final.ledger key = none ∨ ∃ input, record.event = .begin key input ∧
        final.ledger key = some ⟨input, 0, Nat.zero_le _, .pending⟩) := by
  cases record with | mk position event actions =>
    cases actual with
    | begin added input fresh =>
      constructor
      · rfl
      · by_cases same : key = added
        · subst added; exact .inr ⟨input, rfl, by simp [Ledger.set]⟩
        · exact .inl (by simpa only [Ledger.set, ite_eq_right same] using absent)
    | commit added previous stream extent stored live unreturned increase bound writable =>
      by_cases same : key = added
      · subst added; rw [absent] at stored; cases stored
      · exact ⟨by simp [Record.bytesFor, Ne.symm same],
          .inl (by simpa only [Ledger.set, ite_eq_right same] using absent)⟩
    | returned added previous reply stored pending count =>
      by_cases same : key = added
      · subst added; rw [absent] at stored; cases stored
      · exact ⟨rfl, .inl (by simpa only [Ledger.set, ite_eq_right same] using absent)⟩
    | lost added previous stored pending =>
      by_cases same : key = added
      · subst added; rw [absent] at stored; cases stored
      · exact ⟨rfl, .inl (by simpa only [Ledger.set, ite_eq_right same] using absent)⟩
    | channel => exact ⟨rfl, .inl absent⟩

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {ticks : List (ActorTick runtime)} {pair : Pair} {Token : Type}

-- §AR-host-boundary.primitives: An unregistered call cannot have committed
-- bytes. The first real source-entry registration starts at extent zero;
-- every later partial commit is counted once in the actual same history.
theorem ObservedJournal.unregistered_key_bytes
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {position : Nat} {initial final : PhysicalState} {records : List Record}
    (journal : ObservedJournal primitive position initial records final)
    (key : CallKey) (absent : initial.ledger key = none) :
    (final.ledger key = none ∧ records.flatMap (Record.bytesFor key) = []) ∨
      ∃ current, final.ledger key = some current ∧
        records.flatMap (Record.bytesFor key) = current.input.bytes.take current.committed := by
  induction journal with
  | nil => exact .inl ⟨absent, rfl⟩
  | cons order actual tail ih =>
    obtain ⟨empty, none | ⟨input, began, selected⟩⟩ := step_unregistered_key actual.erase key absent
    · rcases ih none with ⟨finalAbsent, bytes⟩ | ⟨current, selected, bytes⟩
      · exact .inl ⟨finalAbsent, by simp only [List.flatMap_cons, empty, List.nil_append, bytes]⟩
      · exact .inr ⟨current, selected, by simp only [List.flatMap_cons, empty, List.nil_append, bytes]⟩
    · obtain ⟨current, stored, same, increased, bytes⟩ := tail.key_bytes key _ selected
      exact .inr ⟨current, stored, by
        simpa only [List.flatMap_cons, empty, List.nil_append, segment, List.drop_zero,
          Nat.sub_zero, same] using bytes⟩

theorem actual_key_committed_prefix
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {final : PhysicalState} {records : List Record}
    (journal : ObservedJournal primitive 0 .unborn records final)
    (key : CallKey) (current : WriteProgress) (selected : final.ledger key = some current) :
    records.flatMap (Record.bytesFor key) = current.input.bytes.take current.committed := by
  rcases journal.unregistered_key_bytes key rfl with ⟨absent, empty⟩ | ⟨last, stored, bytes⟩
  · rw [absent] at selected; cases selected
  · have same := Option.some.inj (stored.symm.trans selected)
    subst last
    exact bytes

end LeanCage.Host.PrivateStreams
