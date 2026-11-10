import GatewayStreamSynchronization

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

-- §FS-host-boundary.caller: Count only the bytes enqueued by this exact
-- source invocation/ordinal. Reply/loss rows carry no new payload.
def Record.bytesFor (key : CallKey) (record : Record) : Bytes :=
  match record.event with
  | .commit selected _ => if selected = key then record.actions.flatMap fun
      | .write _ bytes => bytes
      | _ => []
    else []
  | _ => []

theorem segment_join (bytes : Bytes) {first middle last : Nat}
    (before : first ≤ middle) (after : middle ≤ last) :
    segment bytes first middle ++ segment bytes middle last = segment bytes first last := by
  have count : middle - first + (last - middle) = last - first := by omega
  have next : first + (middle - first) = middle := by omega
  simpa only [segment, List.drop_drop, next, count] using
    (List.take_add (l := bytes.drop first) (i := middle - first) (j := last - middle)).symm

theorem step_key_bytes {initial final : PhysicalState} {record : Record}
    (actual : ProgressStep initial record.event record.actions final)
    (key : CallKey) (current : WriteProgress) (selected : initial.ledger key = some current) :
    ∃ last, final.ledger key = some last ∧ last.input = current.input ∧
      current.committed ≤ last.committed ∧
      record.bytesFor key = segment current.input.bytes current.committed last.committed := by
  cases record with | mk position event actions =>
    cases actual with
    | begin added input fresh =>
      have different : key ≠ added := by intro same; subst added; rw [fresh] at selected; cases selected
      exact ⟨current, by simp only [Ledger.set, ite_eq_right different]; exact selected,
        rfl, Nat.le_refl _, by simp [Record.bytesFor, segment]⟩
    | commit added previous stream extent stored live unreturned increase bound writable =>
      by_cases same : key = added
      · subst added
        have identity := Option.some.inj (stored.symm.trans selected)
        subst previous
        exact ⟨{ current with committed := extent, bounded := bound }, by simp [Ledger.set],
          rfl, Nat.le_of_lt increase, by simp [Record.bytesFor]⟩
      · exact ⟨current, by simp only [Ledger.set, ite_eq_right same]; exact selected,
          rfl, Nat.le_refl _, by simp [Record.bytesFor, Ne.symm same, segment]⟩
    | returned added previous reply stored pending count =>
      by_cases same : key = added
      · subst added
        have identity := Option.some.inj (stored.symm.trans selected)
        subst previous
        exact ⟨{ current with observation := .returned reply }, by simp [Ledger.set],
          rfl, Nat.le_refl _, by simp [Record.bytesFor, segment]⟩
      · exact ⟨current, by simp only [Ledger.set, ite_eq_right same]; exact selected,
          rfl, Nat.le_refl _, by simp [Record.bytesFor, segment]⟩
    | lost added previous stored pending =>
      by_cases same : key = added
      · subst added
        have identity := Option.some.inj (stored.symm.trans selected)
        subst previous
        exact ⟨{ current with observation := .lost }, by simp [Ledger.set],
          rfl, Nat.le_refl _, by simp [Record.bytesFor, segment]⟩
      · exact ⟨current, by simp only [Ledger.set, ite_eq_right same]; exact selected,
          rfl, Nat.le_refl _, by simp [Record.bytesFor, segment]⟩
    | channel => exact ⟨current, selected, rfl, Nat.le_refl _, by simp [Record.bytesFor, segment]⟩

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {ticks : List (ActorTick runtime)} {pair : Pair} {Token : Type}

-- §AR-host-boundary.primitives: Arbitrarily interleaved partial commits
-- telescope to one exact payload prefix; an ACK/loss never adds it again.
theorem ObservedJournal.key_bytes
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {position : Nat} {initial final : PhysicalState} {records : List Record}
    (actual : ObservedJournal primitive position initial records final)
    (key : CallKey) (current : WriteProgress) (selected : initial.ledger key = some current) :
    ∃ last, final.ledger key = some last ∧ last.input = current.input ∧
      current.committed ≤ last.committed ∧
      records.flatMap (Record.bytesFor key) = segment current.input.bytes current.committed last.committed := by
  induction actual generalizing current with
  | nil => exact ⟨current, selected, rfl, Nat.le_refl _, by simp [segment]⟩
  | cons order actual tail ih =>
    obtain ⟨middle, stored, input, progress, bytes⟩ := step_key_bytes actual.erase key current selected
    obtain ⟨last, final, same, increased, rest⟩ := ih middle stored
    refine ⟨last, final, same.trans input, Nat.le_trans progress increased, ?_⟩
    simp only [List.flatMap_cons, bytes, rest, input]
    exact segment_join _ progress increased

-- §FS-host-boundary.caller: For an actual engine call, its completed ACK
-- fixes the concatenation of ALL earlier partial commits to exactly that
-- acknowledged payload prefix, independently of unrelated global events.
theorem actual_engine_ack_bytes
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {entry : EngineWriteEntry ticks pair} {reply : Reply} {initial : PhysicalState}
    (acknowledgement : EngineReconciliation primitive entry (some reply) initial)
    (success : nativeError reply = false)
    (registeredAt : PhysicalState) (token : Token) (_entered : primitive.enteredEngine token entry)
    (_fresh : registeredAt.ledger entry.key = none) {position : Nat} {records : List Record}
    (progress : ObservedJournal primitive position
      { registeredAt with ledger := registeredAt.ledger.set entry.key ⟨entry.description, 0, Nat.zero_le _, .pending⟩ }
      records initial) :
    records.flatMap (Record.bytesFor entry.key) = entry.request.left.data.toList.take reply.1.toNat := by
  have start : (registeredAt.ledger.set entry.key ⟨entry.description, 0, Nat.zero_le _, .pending⟩) entry.key =
      some ⟨entry.description, 0, Nat.zero_le _, .pending⟩ := by simp [Ledger.set]
  obtain ⟨last, stored, input, increased, bytes⟩ := progress.key_bytes entry.key _ start
  have same := Option.some.inj (stored.symm.trans acknowledgement.selected)
  subst last
  have count := acknowledgement.exact.2.2 reply rfl success
  simpa only [segment, count, input, EngineWriteEntry.description, List.drop_zero, Nat.sub_zero] using bytes

-- §AR-host-boundary.primitives: Even a still-pending native send has this
-- exact committed prefix. Its real entry registration precedes these kernel
-- effects, and no later SDK return, product or ACK is required.
theorem actual_native_pending_bytes
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    (entry : NativeWriteEntry process child native hostUid before after callers next ticks pair)
    (registeredAt : PhysicalState) (token : Token) (_entered : primitive.enteredNative token entry)
    (_fresh : registeredAt.ledger entry.key = none) {position : Nat} {records : List Record} {final : PhysicalState}
    (progress : ObservedJournal primitive position
      { registeredAt with ledger := registeredAt.ledger.set entry.key ⟨entry.description, 0, Nat.zero_le _, .pending⟩ }
      records final) :
    ∃ current, final.ledger entry.key = some current ∧ current.input = entry.description ∧
      records.flatMap (Record.bytesFor entry.key) = entry.bytes.data.toList.take current.committed := by
  have start : (registeredAt.ledger.set entry.key ⟨entry.description, 0, Nat.zero_le _, .pending⟩) entry.key =
      some ⟨entry.description, 0, Nat.zero_le _, .pending⟩ := by simp [Ledger.set]
  obtain ⟨last, stored, input, increased, bytes⟩ := progress.key_bytes entry.key _ start
  exact ⟨last, stored, input, by simpa only [segment, NativeWriteEntry.description, List.drop_zero, Nat.sub_zero] using bytes⟩

end LeanCage.Host.PrivateStreams
