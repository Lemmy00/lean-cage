import TransportProofs.Bounds

namespace LeanCage.Host.Transport

def State.Framed (state : State) : Prop :=
  match state.phase with
  | .prefix _ => state.framesRev = [] ∧ state.terminal = none
  | .header _ | .payload _ _ => state.terminal = none
  | .done => ∃ frame earlier terminal, state.framesRev = frame :: earlier ∧
      frame.header.tag = .terminal ∧ Terminal.parse frame.payload = .ok terminal ∧
      state.terminal = some terminal
  | .failed => True

theorem framed_commit (state : State) (none : state.terminal = none) (header : Header)
    (payload : ByteArray) : (state.commit header payload).Framed := by
  unfold State.commit
  cases result : state.commit? header payload with
  | error error => trivial
  | ok next =>
    rcases commit_ok state header payload next result with
      ⟨actual, terminal, _, _, _, _, ended, rfl⟩
    unfold State.nextTerminal at ended
    by_cases last : actual.tag = .terminal
    · simp only [last, ite_true] at ended
      cases parsed : Terminal.parse payload with
      | error error => simp [parsed] at ended
      | ok value =>
        simp only [parsed, Except.ok.injEq] at ended
        cases ended
        simp only [State.append, last, ite_true, State.Framed]
        exact ⟨⟨actual, payload⟩, state.framesRev, value, rfl, last, parsed, rfl⟩
    · simp only [last, ite_false, none, Except.ok.injEq] at ended
      cases ended
      simp only [State.append, last, ite_false, State.Framed]

theorem framed_byte (state : State) (framed : state.Framed) (byte : UInt8) : (state.byte byte).Framed := by
  unfold State.byte
  split
  · exact framed
  · cases phase : state.phase with
    | failed => trivial
    | done => trivial
    | «prefix» matched =>
      have old := framed
      simp only [State.Framed, phase] at old
      dsimp only
      split
      · split
        · by_cases last : matched + 1 = state.expectedPrefix.size
          · simpa only [last, ite_true, State.Framed] using old.2
          · simpa only [last, ite_false, State.Framed] using old
        · trivial
      · trivial
    | header bytes =>
      have old := framed
      simp only [State.Framed, phase] at old
      dsimp only
      split
      · split
        · cases parsed : Header.parse state.limits (bytes.push byte) with
          | error error => trivial
          | ok header =>
            dsimp only
            cases admitted : state.acceptHeader header with
            | error error => trivial
            | ok value =>
              cases value
              dsimp only
              split
              · exact framed_commit state old header ByteArray.empty
              · exact old
        · exact old
      · trivial
    | payload header bytes =>
      have old := framed
      simp only [State.Framed, phase] at old
      dsimp only
      split
      · split
        · exact framed_commit state old header (bytes.push byte)
        · exact old
      · trivial

theorem framed_bytes (state : State) (framed : state.Framed) (bytes : List UInt8) :
    (state.bytes bytes).Framed := by
  induction bytes generalizing state with
  | nil => exact framed
  | cons byte bytes ih => exact ih (state.byte byte) (framed_byte state framed byte)

theorem framed_step (state : State) (framed : state.Framed) (event : Event) : (state.step event).Framed := by
  unfold State.step
  split
  · exact framed
  · cases event with
    | eof => exact framed
    | data bytes =>
      dsimp only
      split
      · trivial
      · split
        · trivial
        · exact framed_bytes state framed bytes.data.toList

theorem framed_run (state : State) (framed : state.Framed) (events : List Event) :
    (state.run events).Framed := by
  induction events generalizing state with
  | nil => exact framed
  | cons event events ih => exact ih (state.step event) (framed_step state framed event)

-- §FS-host-boundary.transport: The ledger retains each actual header and payload in wire order.
def frameWire (frames : List Frame) : List UInt8 :=
  frames.flatMap (fun frame => frame.header.raw.data.toList ++ frame.payload.data.toList)

def State.wire (state : State) : List UInt8 :=
  match state.phase with
  | .prefix matched => state.expectedPrefix.data.toList.take matched
  | .header bytes => state.expectedPrefix.data.toList ++ frameWire state.framesRev.reverse ++ bytes.data.toList
  | .payload parsed bytes => state.expectedPrefix.data.toList ++ frameWire state.framesRev.reverse ++
      parsed.raw.data.toList ++ bytes.data.toList
  | .done | .failed => state.expectedPrefix.data.toList ++ frameWire state.framesRev.reverse

theorem append_wire (state : State) (header : Header) (payload : ByteArray) (terminal : Option Terminal) :
    (state.append header payload terminal).wire = state.expectedPrefix.data.toList ++
      frameWire state.framesRev.reverse ++ header.raw.data.toList ++ payload.data.toList := by
  by_cases last : header.tag = .terminal <;>
    simp [State.append, last, State.wire, List.reverse_cons, frameWire, List.append_assoc]

theorem commit_wire (state : State) (header : Header) (payload : ByteArray)
    (clean : (state.commit header payload).error = none) :
    (state.commit header payload).wire = state.expectedPrefix.data.toList ++
      frameWire state.framesRev.reverse ++ header.raw.data.toList ++ payload.data.toList := by
  unfold State.commit at *
  cases result : state.commit? header payload with
  | error error => simp only [result, State.fail] at clean; contradiction
  | ok next =>
    rcases commit_ok state header payload next result with
      ⟨actual, terminal, parsed, _, _, _, _, rfl⟩
    rw [append_wire, (header_parse_fields _ _ _ parsed).2.2.1]

private theorem push_list (bytes : ByteArray) (byte : UInt8) :
    (bytes.push byte).data.toList = bytes.data.toList ++ [byte] := by
  simp only [ByteArray.data_push, Array.toList_push]

private theorem take_byte (bytes : ByteArray) (matched : Nat) (byte : UInt8)
    (within : matched < bytes.size) (equal : bytes[matched]! = byte) :
    bytes.data.toList.take (matched + 1) = bytes.data.toList.take matched ++ [byte] := by
  have withinList : matched < bytes.data.toList.length := by simpa using within
  rw [List.take_add_one, List.getElem?_eq_getElem withinList]
  have value : bytes.data.toList[matched] = byte := by
    rw [Array.getElem_toList withinList, ← ByteArray.getElem_eq_getElem_data,
      ← getElem!_pos bytes matched within, equal]
  simp only [value, Option.toList_some]

theorem byte_clean_before (state : State) (byte : UInt8) (clean : (state.byte byte).error = none) :
    state.error = none := by
  cases error : state.error with
  | none => rfl
  | some failure =>
    rw [byte_error state byte failure error, error] at clean
    contradiction

theorem byte_wire (state : State) (framed : state.Framed) (byte : UInt8)
    (clean : (state.byte byte).error = none) : (state.byte byte).wire = state.wire ++ [byte] := by
  have prior := byte_clean_before state byte clean
  simp only [State.byte, prior, Option.isSome_none, Bool.false_eq_true, ite_false] at clean ⊢
  cases phase : state.phase with
  | failed => simp only [phase, State.fail] at clean; contradiction
  | done => simp only [phase, State.fail] at clean; contradiction
  | «prefix» matched =>
    have empty := framed
    simp only [State.Framed, phase] at empty
    simp only [phase] at clean ⊢
    by_cases within : matched < state.expectedPrefix.size
    · simp only [within, ite_true] at clean ⊢
      by_cases equal : state.expectedPrefix[matched]! = byte
      · simp only [equal, ite_true]
        by_cases last : matched + 1 = state.expectedPrefix.size
        · have full : matched + 1 = state.expectedPrefix.data.toList.length := by simpa using last
          have identity := take_byte state.expectedPrefix matched byte within equal
          rw [full, List.take_length] at identity
          simpa only [last, ite_true, State.wire, phase, empty.1, List.reverse_nil, frameWire,
            List.flatMap_nil, ByteArray.data_empty, Array.toList_empty, List.append_nil] using identity
        · simpa only [last, ite_false, State.wire, phase] using
            take_byte state.expectedPrefix matched byte within equal
      · simp only [equal, ite_false, State.fail] at clean
        contradiction
    · simp only [within, ite_false, State.fail] at clean
      contradiction
  | header bytes =>
    simp only [phase] at clean ⊢
    by_cases within : bytes.size < 16
    · simp only [within, ite_true] at clean ⊢
      by_cases full : (bytes.push byte).size = 16
      · simp only [full, ite_true] at clean ⊢
        cases parsed : Header.parse state.limits (bytes.push byte) with
        | error error => simp only [parsed, State.fail] at clean; contradiction
        | ok header =>
          simp only [parsed] at clean
          dsimp only
          cases admitted : state.acceptHeader header with
          | error error => simp only [admitted, State.fail] at clean; contradiction
          | ok value =>
            cases value
            simp only [admitted] at clean
            dsimp only
            by_cases zero : header.length = 0
            · simp only [zero, ite_true] at clean ⊢
              rw [commit_wire state header ByteArray.empty clean,
                (header_parse_fields _ _ _ parsed).2.2.1]
              simp only [State.wire, phase, push_list, ByteArray.data_empty, Array.toList_empty,
                List.append_nil, List.append_assoc]
            · simp only [zero, ite_false, State.wire,
                (header_parse_fields _ _ _ parsed).2.2.1, phase, push_list, ByteArray.data_empty,
                Array.toList_empty, List.append_nil, List.append_assoc]
      · simp only [full, ite_false, State.wire, phase, push_list, List.append_assoc]
    · simp only [within, ite_false, State.fail] at clean
      contradiction
  | payload header bytes =>
    simp only [phase] at clean ⊢
    by_cases within : (decide (bytes.size < header.length) &&
        decide (header.length ≤ activeBudget state.limits)) = true
    · simp only [within, ite_true] at clean ⊢
      by_cases full : (bytes.push byte).size = header.length
      · simp only [full, ite_true] at clean ⊢
        rw [commit_wire state header (bytes.push byte) clean]
        simp only [State.wire, phase, push_list, List.append_assoc]
      · simp only [full, ite_false, State.wire, phase, push_list, List.append_assoc]
    · simp only [within, State.fail] at clean
      contradiction

theorem bytes_error (state : State) (bytes : List UInt8) (error : Error)
    (failed : state.error = some error) : state.bytes bytes = state := by
  induction bytes with
  | nil => rfl
  | cons byte bytes ih =>
    simp only [State.bytes, List.foldl_cons, byte_error state byte error failed]
    exact ih

theorem bytes_clean_before (state : State) (bytes : List UInt8)
    (clean : (state.bytes bytes).error = none) : state.error = none := by
  cases error : state.error with
  | none => rfl
  | some failure =>
    rw [bytes_error state bytes failure error, error] at clean
    contradiction

theorem bytes_wire (state : State) (framed : state.Framed) (bytes : List UInt8)
    (clean : (state.bytes bytes).error = none) : (state.bytes bytes).wire = state.wire ++ bytes := by
  induction bytes generalizing state with
  | nil => simp [State.bytes]
  | cons byte bytes ih =>
    change ((state.byte byte).bytes bytes).error = none at clean
    have firstClean := bytes_clean_before (state.byte byte) bytes clean
    change ((state.byte byte).bytes bytes).wire = _
    rw [ih (state.byte byte) (framed_byte state framed byte) clean,
      byte_wire state framed byte firstClean]
    simp only [List.append_assoc, List.singleton_append]

def Event.wire : Event → List UInt8
  | .data bytes => bytes.data.toList
  | .eof => []

def eventsWire (events : List Event) : List UInt8 := events.flatMap Event.wire

theorem step_clean_before (state : State) (event : Event) (clean : (state.step event).error = none) :
    state.error = none := by
  cases error : state.error with
  | none => rfl
  | some failure =>
    rw [step_error state event failure error, error] at clean
    contradiction

theorem run_clean_before (state : State) (events : List Event) (clean : (state.run events).error = none) :
    state.error = none := by
  cases error : state.error with
  | none => rfl
  | some failure =>
    rw [run_error state events failure error, error] at clean
    contradiction

theorem step_wire (state : State) (framed : state.Framed) (event : Event)
    (clean : (state.step event).error = none) : (state.step event).wire = state.wire ++ event.wire := by
  have prior := step_clean_before state event clean
  simp only [State.step, prior, Option.isSome_none, Bool.false_eq_true, ite_false] at clean ⊢
  cases event with
  | eof =>
    simp only [Event.wire, List.append_nil]
    cases phase : state.phase <;> simp only [State.wire, phase]
  | data bytes =>
    dsimp only at clean ⊢
    by_cases large : chunkMax < bytes.size
    · simp only [large, ite_true, State.fail] at clean
      contradiction
    · simp only [large, ite_false] at clean ⊢
      by_cases eof : state.observedEof = true
      · simp only [eof, ite_true, State.fail] at clean
        contradiction
      · simp only [eof]
        simp only [eof] at clean
        exact bytes_wire state framed bytes.data.toList clean

theorem run_wire (state : State) (framed : state.Framed) (events : List Event)
    (clean : (state.run events).error = none) : (state.run events).wire = state.wire ++ eventsWire events := by
  induction events generalizing state with
  | nil => simp [State.run, eventsWire]
  | cons event events ih =>
    change ((state.step event).run events).error = none at clean
    have firstClean := run_clean_before (state.step event) events clean
    change ((state.step event).run events).wire = _
    rw [ih (state.step event) (framed_step state framed event) clean,
      step_wire state framed event firstClean]
    simp only [eventsWire, List.flatMap_cons, List.append_assoc]

-- §FS-host-boundary.transport: Fixed caller identities survive every decoder update.
theorem commit_preserves {α : Type} (view : State → α)
    (fail : ∀ state error, view (state.fail error) = view state)
    (append : ∀ state header payload terminal, view (state.append header payload terminal) = view state)
    (state : State) (header : Header) (payload : ByteArray) :
    view (state.commit header payload) = view state := by
  unfold State.commit
  cases result : state.commit? header payload with
  | error error => exact fail state error
  | ok next =>
    rcases commit_ok state header payload next result with
      ⟨actual, terminal, _, _, _, _, _, rfl⟩
    exact append state actual payload terminal

theorem byte_preserves {α : Type} (view : State → α)
    (fail : ∀ state error, view (state.fail error) = view state)
    (phaseUpdate : ∀ state phase, view { state with phase } = view state)
    (append : ∀ state header payload terminal, view (state.append header payload terminal) = view state)
    (state : State) (byte : UInt8) : view (state.byte byte) = view state := by
  unfold State.byte
  split
  · rfl
  · cases phase : state.phase with
    | failed => exact fail state .incomplete
    | done => exact fail state .trailing
    | «prefix» matched =>
      dsimp only
      split
      · split
        · exact phaseUpdate state _
        · exact fail state .identity
      · exact fail state .identity
    | header bytes =>
      dsimp only
      split
      · split
        · cases parsed : Header.parse state.limits (bytes.push byte) with
          | error error => exact fail state error
          | ok header =>
            dsimp only
            cases admitted : state.acceptHeader header with
            | error error => exact fail state error
            | ok value =>
              cases value
              dsimp only
              split
              · exact commit_preserves view fail append state header ByteArray.empty
              · exact phaseUpdate state _
        · exact phaseUpdate state _
      · exact fail state .header
    | payload header bytes =>
      dsimp only
      split
      · split
        · exact commit_preserves view fail append state header (bytes.push byte)
        · exact phaseUpdate state _
      · exact fail state .header

theorem byte_static (state : State) (byte : UInt8) :
    ((state.byte byte).limits, (state.byte byte).expectedPrefix, (state.byte byte).observedEof) =
      (state.limits, state.expectedPrefix, state.observedEof) := by
  exact byte_preserves (fun value => (value.limits, value.expectedPrefix, value.observedEof))
    (by intros; rfl) (by intros; rfl) (by intros; rfl) state byte

theorem bytes_static (state : State) (bytes : List UInt8) :
    ((state.bytes bytes).limits, (state.bytes bytes).expectedPrefix, (state.bytes bytes).observedEof) =
      (state.limits, state.expectedPrefix, state.observedEof) := by
  induction bytes generalizing state with
  | nil => rfl
  | cons byte bytes ih => exact (ih (state.byte byte)).trans (byte_static state byte)

theorem step_config (state : State) (event : Event) :
    ((state.step event).limits, (state.step event).expectedPrefix) =
      (state.limits, state.expectedPrefix) := by
  unfold State.step
  split
  · rfl
  · cases event with
    | eof => rfl
    | data bytes =>
      dsimp only
      split
      · rfl
      · split
        · rfl
        · have result := bytes_static state bytes.data.toList
          exact congrArg (fun value => (value.1, value.2.1)) result

theorem run_config (state : State) (events : List Event) :
    ((state.run events).limits, (state.run events).expectedPrefix) =
      (state.limits, state.expectedPrefix) := by
  induction events generalizing state with
  | nil => rfl
  | cons event events ih => exact (ih (state.step event)).trans (step_config state event)

-- §FS-host-boundary.transport: Fragment boundaries disappear into one actual byte sequence.
theorem data_fragmentation (state : State) (first second : ByteArray)
    (clean : state.error = none) (live : state.observedEof = false)
    (smallFirst : first.size ≤ chunkMax) (smallSecond : second.size ≤ chunkMax)
    (smallCombined : (first ++ second).size ≤ chunkMax) :
    state.step (.data (first ++ second)) = (state.step (.data first)).step (.data second) := by
  have appendBytes := bytes_append state first.data.toList second.data.toList
  have eof_preserved := congrArg (fun value => value.2.2) (bytes_static state first.data.toList)
  change (state.bytes first.data.toList).observedEof = state.observedEof at eof_preserved
  simp only [State.step, clean, Option.isSome_none, Bool.false_eq_true, ite_false,
    Nat.not_lt.mpr smallFirst, Nat.not_lt.mpr smallCombined, live,
    ByteArray.toList_data_append, appendBytes]
  cases failure : (state.bytes first.data.toList).error with
  | some error =>
    rw [bytes_error _ _ error failure]
    simp only [Option.isSome_some, ite_true]
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, ite_false,
      Nat.not_lt.mpr smallSecond, eof_preserved, live]

theorem data_step_eq_bytes (state : State) (bytes : ByteArray) (live : state.observedEof = false)
    (bounded : bytes.size ≤ chunkMax) : state.step (.data bytes) = state.bytes bytes.data.toList := by
  cases error : state.error with
  | some failure => rw [step_error state (.data bytes) failure error, bytes_error state _ failure error]
  | none =>
    simp only [State.step, error, Option.isSome_none, Bool.false_eq_true, ite_false,
      Nat.not_lt.mpr bounded, live]

-- §FS-host-boundary.transport: All bounded fragmentations have the same complete execution.
theorem data_normal_form (state : State) (chunks : List ByteArray) (live : state.observedEof = false)
    (bounded : ∀ chunk ∈ chunks, chunk.size ≤ chunkMax) :
    state.run (chunks.map Event.data) = state.bytes (chunks.flatMap (·.data.toList)) := by
  induction chunks generalizing state with
  | nil => rfl
  | cons chunk chunks ih =>
    change (state.step (.data chunk)).run (chunks.map Event.data) = _
    rw [data_step_eq_bytes state chunk live (bounded chunk (by simp))]
    have eof := congrArg (fun value => value.2.2) (bytes_static state chunk.data.toList)
    have nextLive : (state.bytes chunk.data.toList).observedEof = false := eof.trans live
    rw [ih (state.bytes chunk.data.toList) nextLive (fun item member => bounded item (by simp [member]))]
    exact (bytes_append state chunk.data.toList (chunks.flatMap (·.data.toList))).symm

theorem arbitrary_fragmentation (state : State) (first second : List ByteArray)
    (live : state.observedEof = false) (firstBound : ∀ chunk ∈ first, chunk.size ≤ chunkMax)
    (secondBound : ∀ chunk ∈ second, chunk.size ≤ chunkMax)
    (sameBytes : first.flatMap (·.data.toList) = second.flatMap (·.data.toList)) :
    state.run (first.map Event.data) = state.run (second.map Event.data) := by
  rw [data_normal_form state first live firstBound, data_normal_form state second live secondBound, sameBytes]

end LeanCage.Host.Transport
