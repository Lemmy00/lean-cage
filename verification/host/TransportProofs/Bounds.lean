import LeanCageHost.Transport
import BytesProofs
import Std.Data.TreeSet.Lemmas

namespace LeanCage.Host.Transport

-- §FS-host-boundary.transport: Rejected bytes cannot be repaired by a valid suffix.
theorem step_error (state : State) (event : Event) (error : Error)
    (failed : state.error = some error) : state.step event = state := by
  simp [State.step, failed]

theorem byte_error (state : State) (byte : UInt8) (error : Error)
    (failed : state.error = some error) : state.byte byte = state := by
  simp [State.byte, failed]

theorem run_error (state : State) (events : List Event) (error : Error)
    (failed : state.error = some error) : state.run events = state := by
  induction events with
  | nil => rfl
  | cons event events ih =>
    simp only [State.run, List.foldl_cons, step_error state event error failed]
    exact ih

theorem fail_report (state : State) (error : Error) : (state.fail error).report? = state.report? := rfl

theorem oversized_chunk (state : State) (bytes : ByteArray)
    (clean : state.error = none) (large : chunkMax < bytes.size) :
    state.step (.data bytes) = state.fail .chunk := by
  simp [State.step, clean, large]

theorem bytes_append (state : State) (first second : List UInt8) :
    state.bytes (first ++ second) = (state.bytes first).bytes second := by
  simp [State.bytes, List.foldl_append]

-- §FS-host-boundary.transport: Successful framing consumes every header field at full width.
theorem header_parse_fields (limits : Limits) (bytes : ByteArray) (header : Header)
    (accepted : Header.parse limits bytes = .ok header) :
    bytes.size = 16 ∧ word bytes 4 4 = 0 ∧ header.raw = bytes ∧
      Tag.ofCode (word bytes 0 4) = some header.tag ∧ header.length = word bytes 8 8 ∧
      header.length ≤ header.tag.cap limits := by
  unfold Header.parse at accepted
  split at accepted
  · rename_i shape
    cases code : Tag.ofCode (word bytes 0 4) with
    | none => simp [code] at accepted
    | some tag =>
      rw [code] at accepted
      dsimp only at accepted
      split at accepted
      · rename_i cap
        split at accepted
        · contradiction
        · split at accepted
          · contradiction
          · cases accepted
            simp_all
      · contradiction
  · contradiction

-- §FS-host-boundary.transport: A terminal marker alone never completes a live channel.
theorem finish_requires_eof (state : State) (result : Result)
    (accepted : state.finish = .ok result) : state.observedEof = true := by
  cases error : state.error with
  | some failure => simp [State.finish, error] at accepted
  | none =>
    cases eof : state.observedEof with
    | false => simp [State.finish, error, eof] at accepted
    | true => rfl

theorem finish_clean (state : State) (result : Result)
    (accepted : state.finish = .ok result) : state.error = none := by
  cases error : state.error with
  | some failure => simp [State.finish, error] at accepted
  | none => rfl

theorem init_fields (request bundle : ByteArray) (limits : Limits) (state : State)
    (accepted : State.init request bundle limits = .ok state) :
    limits.Valid ∧ request.size = 32 ∧ bundle.size = 64 ∧
      ascii request = true ∧ ascii bundle = true ∧
      state = { limits, expectedPrefix := identityPrefix request bundle, phase := .prefix 0 } := by
  unfold State.init at accepted
  split at accepted
  · rename_i valid
    split at accepted
    · rename_i identities
      cases accepted
      exact ⟨valid, identities.1, identities.2.1, identities.2.2.1, identities.2.2.2, rfl⟩
    · contradiction
  · contradiction

theorem prefix_size (request bundle : ByteArray) (requestSize : request.size = 32)
    (bundleSize : bundle.size = 64) : (identityPrefix request bundle).size = 104 := by
  unfold identityPrefix
  rw [ByteArray.size_append, ByteArray.size_append, requestSize, bundleSize]
  rfl

theorem cap_le_active (limits : Limits) (valid : limits.Valid) (tag : Tag) :
    tag.cap limits ≤ activeBudget limits := by
  rcases valid with ⟨outBound, errBound, workBound, inodeBound⟩
  cases tag <;> simp only [Tag.cap, activeBudget]
  all_goals simp only [reportMax, captureMax, manifestMax] at *
  all_goals omega

theorem acceptHeader_fields (state : State) (header : Header)
    (accepted : state.acceptHeader header = .ok ()) :
    state.retainedBytes + 16 + header.length ≤ retainedBudget state.limits ∧
      (header.tag = .blob → state.blobCount + 1 ≤ state.limits.inodesMax ∧
        state.blobBytes + (header.length - 64) ≤ state.limits.workspaceMax) ∧
      (header.tag ≠ .blob → state.normalCount + 1 ≤ 6 ∧ state.seen header.tag = false) := by
  unfold State.acceptHeader at accepted
  dsimp only at accepted
  split at accepted
  · rename_i blob
    split at accepted
    · rename_i bounds
      exact ⟨bounds.2.2, fun _ => ⟨bounds.1, bounds.2.1⟩, fun notBlob => False.elim (notBlob blob)⟩
    · contradiction
  · rename_i notBlob
    split at accepted
    · contradiction
    · rename_i unseen
      split at accepted
      · rename_i bounds
        exact ⟨bounds.2, fun blob => False.elim (notBlob blob), fun _ => ⟨bounds.1, by simpa using unseen⟩⟩
      · contradiction

-- §FS-host-boundary.transport: A completed frame has the same actual parsed header and bytes.
theorem commit_ok (state : State) (header : Header) (payload : ByteArray) (next : State)
    (accepted : state.commit? header payload = .ok next) :
    ∃ actual terminal,
      Header.parse state.limits header.raw = .ok actual ∧ state.acceptHeader actual = .ok () ∧
      payload.size = actual.length ∧ state.acceptBlob actual payload = .ok () ∧
      state.nextTerminal actual payload = .ok terminal ∧ next = state.append actual payload terminal := by
  unfold State.commit? at accepted
  cases parsed : Header.parse state.limits header.raw with
  | error failure => simp [parsed] at accepted
  | ok actual =>
    rw [parsed] at accepted
    dsimp only at accepted
    cases admitted : state.acceptHeader actual with
    | error failure => simp [admitted] at accepted
    | ok value =>
      cases value
      rw [admitted] at accepted
      dsimp only at accepted
      split at accepted
      · rename_i length
        cases blob : state.acceptBlob actual payload with
        | error failure => simp [blob] at accepted
        | ok value =>
          cases value
          rw [blob] at accepted
          dsimp only at accepted
          cases ended : state.nextTerminal actual payload with
          | error failure => simp [ended] at accepted
          | ok terminal =>
            simp only [ended, Except.ok.injEq] at accepted
            exact ⟨actual, terminal, rfl, admitted, length, blob, ended, accepted.symm⟩
      · contradiction

theorem header_parse_self (limits : Limits) (bytes : ByteArray) (header : Header)
    (accepted : Header.parse limits bytes = .ok header) : Header.parse limits header.raw = .ok header := by
  have fields := header_parse_fields limits bytes header accepted
  rw [fields.2.2.1]
  exact accepted

theorem header_word64 (limits : Limits) (bytes : ByteArray) (header : Header)
    (accepted : Header.parse limits bytes = .ok header) : header.length < 256 ^ 8 := by
  have fields := header_parse_fields limits bytes header accepted
  have bound := fromLittleEndian_bound (bytes.extract 8 16)
  rw [ByteArray.size_extract, fields.1] at bound
  simpa only [word, fields.2.2.2.2.1, Nat.min_self] using bound

theorem acceptBlob_fields (state : State) (header : Header) (payload : ByteArray)
    (accepted : state.acceptBlob header payload = .ok ()) (blob : header.tag = .blob) :
    (payload.extract 0 64).size = 64 ∧ lowerHex (payload.extract 0 64) = true ∧
      state.seenBlob (payload.extract 0 64) = false := by
  unfold State.acceptBlob at accepted
  simp only [blob, ite_true] at accepted
  split at accepted
  · rename_i valid
    split at accepted
    · contradiction
    · rename_i unseen
      exact ⟨valid.1, valid.2, by simpa using unseen⟩
  · contradiction

def Frame.Valid (limits : Limits) (frame : Frame) : Prop :=
  Header.parse limits frame.header.raw = .ok frame.header ∧ frame.payload.size = frame.header.length ∧
    (frame.header.tag = .blob → frame.blobKey.size = 64 ∧ lowerHex frame.blobKey = true)

def frameCost (frames : List Frame) : Nat :=
  frames.foldr (fun frame total => frame.header.raw.size + frame.payload.size + total) 0

def blobCountOf (frames : List Frame) : Nat :=
  frames.foldr (fun frame count => (if frame.header.tag = .blob then 1 else 0) + count) 0

def normalCountOf (frames : List Frame) : Nat :=
  frames.foldr (fun frame count => (if frame.header.tag = .blob then 0 else 1) + count) 0

def blobBytesOf (frames : List Frame) : Nat :=
  frames.foldr (fun frame total => (if frame.header.tag = .blob then frame.payload.size - 64 else 0) + total) 0

def Phase.Bounded (phase : Phase) (state : State) : Prop :=
  match phase with
  | .prefix matched => matched ≤ state.expectedPrefix.size
  | .header bytes => bytes.size ≤ 16
  | .payload parsedHeader bytes => parsedHeader.raw.size = 16 ∧ bytes.size ≤ parsedHeader.length ∧
      parsedHeader.length ≤ activeBudget state.limits
  | .done | .failed => True

-- §FS-host-boundary.transport: Accounting measures actual retained bytes and list nodes.
structure State.Bounded (state : State) : Prop where
  limits : state.limits.Valid
  identity : state.expectedPrefix.size = 104
  frameValid : ∀ frame ∈ state.framesRev, frame.Valid state.limits
  cost : frameCost state.framesRev = state.retainedBytes
  blobCount : blobCountOf state.framesRev = state.blobCount
  normalCount : normalCountOf state.framesRev = state.normalCount
  blobBytes : blobBytesOf state.framesRev = state.blobBytes
  blobBound : state.blobCount ≤ state.limits.inodesMax
  normalBound : state.normalCount ≤ 6
  bytesBound : state.blobBytes ≤ state.limits.workspaceMax
  retainedBound : state.retainedBytes ≤ retainedBudget state.limits
  indexBound : state.blobKeys.size ≤ state.blobCount
  phase : state.phase.Bounded state

theorem bounded_fail (state : State) (bound : state.Bounded) (error : Error) :
    (state.fail error).Bounded := by
  rcases bound with ⟨limits, identity, frames, cost, blobs, normals, bytes, blobBound, normalBound,
    bytesBound, retainedBound, indexBound, phase⟩
  exact ⟨limits, identity, frames, cost, blobs, normals, bytes, blobBound, normalBound,
    bytesBound, retainedBound, indexBound, True.intro⟩

theorem bounded_init (request bundle : ByteArray) (limits : Limits) (state : State)
    (accepted : State.init request bundle limits = .ok state) : state.Bounded := by
  rcases init_fields request bundle limits state accepted with ⟨valid, requestSize, bundleSize, _, _, rfl⟩
  refine ⟨valid, prefix_size request bundle requestSize bundleSize, ?_, rfl, rfl, rfl, rfl,
    Nat.zero_le _, by change 0 ≤ 6; omega, Nat.zero_le _, Nat.zero_le _, ?_, ?_⟩
  · simp
  · simp
  · simp [Phase.Bounded]

theorem bounded_append (state : State) (bound : state.Bounded) (header : Header) (payload : ByteArray)
    (terminal : Option Terminal) (parsed : Header.parse state.limits header.raw = .ok header)
    (accepted : state.acceptHeader header = .ok ()) (length : payload.size = header.length)
    (blobAccepted : state.acceptBlob header payload = .ok ()) :
    (state.append header payload terminal).Bounded := by
  have fields := header_parse_fields state.limits header.raw header parsed
  have headerSize : header.raw.size = 16 := fields.1
  have admission := acceptHeader_fields state header accepted
  have frameValid : (Frame.mk header payload).Valid state.limits := by
    refine ⟨parsed, length, ?_⟩
    intro blob
    have facts := acceptBlob_fields state header payload blobAccepted blob
    exact ⟨facts.1, facts.2.1⟩
  refine ⟨bound.limits, bound.identity, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro frame member
    simp only [State.append, List.mem_cons] at member
    rcases member with rfl | previous
    · exact frameValid
    · exact bound.frameValid frame previous
  · change header.raw.size + payload.size + frameCost state.framesRev = state.retainedBytes + 16 + payload.size
    rw [bound.cost, headerSize]
    omega
  · change (if header.tag = .blob then 1 else 0) + blobCountOf state.framesRev = state.blobCount + (if header.tag = .blob then 1 else 0)
    rw [bound.blobCount]
    omega
  · change (if header.tag = .blob then 0 else 1) + normalCountOf state.framesRev = state.normalCount + (if header.tag = .blob then 0 else 1)
    rw [bound.normalCount]
    omega
  · change (if header.tag = .blob then payload.size - 64 else 0) + blobBytesOf state.framesRev = state.blobBytes + (if header.tag = .blob then payload.size - 64 else 0)
    rw [bound.blobBytes]
    omega
  · by_cases blob : header.tag = .blob
    · simpa only [State.append, blob, ite_true] using (admission.2.1 blob).1
    · simpa only [State.append, blob, ite_false, Nat.add_zero] using bound.blobBound
  · by_cases blob : header.tag = .blob
    · simpa only [State.append, blob, ite_true, Nat.add_zero] using bound.normalBound
    · simpa only [State.append, blob, ite_false] using (admission.2.2 blob).1
  · by_cases blob : header.tag = .blob
    · simpa only [State.append, blob, ite_true, length] using (admission.2.1 blob).2
    · simpa only [State.append, blob, ite_false, Nat.add_zero] using bound.bytesBound
  · simpa only [State.append, length] using admission.1
  · by_cases blob : header.tag = .blob
    · simp only [State.append, blob, ite_true]
      exact Nat.le_trans Std.TreeSet.size_insert_le (Nat.add_le_add_right bound.indexBound 1)
    · simpa only [State.append, blob, ite_false, Nat.add_zero] using bound.indexBound
  · change (if header.tag = .terminal then Phase.done else .header ByteArray.empty).Bounded _
    split <;> simp [Phase.Bounded]

theorem bounded_commit (state : State) (bound : state.Bounded) (header : Header) (payload : ByteArray) :
    (state.commit header payload).Bounded := by
  unfold State.commit
  cases result : state.commit? header payload with
  | error error => exact bounded_fail state bound error
  | ok next =>
    rcases commit_ok state header payload next result with
      ⟨actual, terminal, parsed, admitted, length, blob, _, rfl⟩
    exact bounded_append state bound actual payload terminal (header_parse_self _ _ _ parsed)
      admitted length blob

theorem bounded_phase (state : State) (bound : state.Bounded) (phase : Phase)
    (bounded : phase.Bounded state) : ({ state with phase }).Bounded := by
  exact { bound with phase := bounded }

-- §FS-host-boundary.transport: Every individual hostile byte preserves the accounting bounds.
theorem bounded_byte (state : State) (bound : state.Bounded) (byte : UInt8) :
    (state.byte byte).Bounded := by
  unfold State.byte
  split
  · exact bound
  · cases phase : state.phase with
    | failed => exact bounded_fail state bound .incomplete
    | done => exact bounded_fail state bound .trailing
    | «prefix» matched =>
      dsimp only
      split
      · rename_i within
        split
        · apply bounded_phase state bound
          split
          · simp [Phase.Bounded]
          · simp only [Phase.Bounded]
            omega
        · exact bounded_fail state bound .identity
      · exact bounded_fail state bound .identity
    | header bytes =>
      dsimp only
      split
      · rename_i within
        split
        · cases parsed : Header.parse state.limits (bytes.push byte) with
          | error error => exact bounded_fail state bound error
          | ok header =>
            dsimp only
            cases admitted : state.acceptHeader header with
            | error error => exact bounded_fail state bound error
            | ok value =>
              cases value
              dsimp only
              split
              · exact bounded_commit state bound header ByteArray.empty
              · apply bounded_phase state bound
                have own := header_parse_self _ _ _ parsed
                exact ⟨(header_parse_fields _ _ _ own).1, Nat.zero_le _,
                  Nat.le_trans (header_parse_fields _ _ _ parsed).2.2.2.2.2
                    (cap_le_active _ bound.limits _)⟩
        · apply bounded_phase state bound
          simp only [Phase.Bounded, ByteArray.size_push]
          omega
      · exact bounded_fail state bound .header
    | payload header bytes =>
      dsimp only
      split
      · rename_i within
        have guards : bytes.size < header.length ∧ header.length ≤ activeBudget state.limits := by
          simpa only [Bool.and_eq_true, decide_eq_true_eq] using within
        split
        · exact bounded_commit state bound header (bytes.push byte)
        · apply bounded_phase state bound
          have oldBound := bound.phase
          rw [phase] at oldBound
          exact ⟨oldBound.1, by simp only [ByteArray.size_push]; omega, guards.2⟩
      · exact bounded_fail state bound .header

theorem bounded_bytes (state : State) (bound : state.Bounded) (bytes : List UInt8) :
    (state.bytes bytes).Bounded := by
  induction bytes generalizing state with
  | nil => exact bound
  | cons byte bytes ih => exact ih (state.byte byte) (bounded_byte state bound byte)

theorem bounded_step (state : State) (bound : state.Bounded) (event : Event) :
    (state.step event).Bounded := by
  unfold State.step
  split
  · exact bound
  · cases event with
    | eof =>
      exact ⟨bound.limits, bound.identity, bound.frameValid, bound.cost, bound.blobCount,
        bound.normalCount, bound.blobBytes, bound.blobBound, bound.normalBound, bound.bytesBound,
        bound.retainedBound, bound.indexBound, bound.phase⟩
    | data bytes =>
      dsimp only
      split
      · exact bounded_fail state bound .chunk
      · split
        · exact bounded_fail state bound .afterEof
        · exact bounded_bytes state bound bytes.data.toList

theorem bounded_run (state : State) (bound : state.Bounded) (events : List Event) :
    (state.run events).Bounded := by
  induction events generalizing state with
  | nil => exact bound
  | cons event events ih => exact ih (state.step event) (bounded_step state bound event)

theorem frame_count (frames : List Frame) : frames.length = blobCountOf frames + normalCountOf frames := by
  induction frames with
  | nil => rfl
  | cons frame frames ih =>
    simp only [List.length_cons, blobCountOf, normalCountOf, List.foldr_cons]
    change _ = (if frame.header.tag = .blob then 1 else 0) + blobCountOf frames +
      ((if frame.header.tag = .blob then 0 else 1) + normalCountOf frames)
    split <;> omega

theorem bounded_storage (state : State) (bound : state.Bounded) :
    frameCost state.framesRev ≤ retainedBudget state.limits ∧
    state.framesRev.length ≤ 6 + state.limits.inodesMax ∧
    blobBytesOf state.framesRev ≤ state.limits.workspaceMax ∧
    state.blobKeys.size ≤ state.limits.inodesMax := by
  refine ⟨bound.cost ▸ bound.retainedBound, ?_, bound.blobBytes ▸ bound.bytesBound,
    Nat.le_trans bound.indexBound bound.blobBound⟩
  rw [frame_count, bound.blobCount, bound.normalCount]
  have blobs := bound.blobBound
  have normals := bound.normalBound
  omega

theorem tag_beq (first second : Tag) : (first == second) = true ↔ first = second := by
  cases first <;> cases second <;> decide

instance : LawfulBEq Tag where
  eq_of_beq := fun equal => (tag_beq _ _).mp equal
  rfl := by intro tag; cases tag <;> rfl

-- §FS-host-boundary.transport: Ledger invariants apply to the same source decoder operations.
theorem ledger_commit (property : List Frame → Std.TreeSet Nat compare → Prop)
    (state : State) (base : property state.framesRev state.blobKeys)
    (append : ∀ header payload terminal, Header.parse state.limits header.raw = .ok header →
      state.acceptHeader header = .ok () → payload.size = header.length →
      state.acceptBlob header payload = .ok () →
      property (state.append header payload terminal).framesRev (state.append header payload terminal).blobKeys)
    (header : Header) (payload : ByteArray) :
    property (state.commit header payload).framesRev (state.commit header payload).blobKeys := by
  unfold State.commit
  cases result : state.commit? header payload with
  | error error => exact base
  | ok next =>
    rcases commit_ok state header payload next result with
      ⟨actual, terminal, parsed, admitted, length, blob, _, rfl⟩
    exact append actual payload terminal (header_parse_self _ _ _ parsed) admitted length blob

theorem ledger_byte (property : List Frame → Std.TreeSet Nat compare → Prop)
    (state : State) (base : property state.framesRev state.blobKeys)
    (append : ∀ header payload terminal, Header.parse state.limits header.raw = .ok header →
      state.acceptHeader header = .ok () → payload.size = header.length →
      state.acceptBlob header payload = .ok () →
      property (state.append header payload terminal).framesRev (state.append header payload terminal).blobKeys)
    (byte : UInt8) : property (state.byte byte).framesRev (state.byte byte).blobKeys := by
  unfold State.byte
  split
  · exact base
  · cases phase : state.phase with
    | failed => exact base
    | done => exact base
    | «prefix» matched =>
      dsimp only
      split
      · split
        · exact base
        · exact base
      · exact base
    | header bytes =>
      dsimp only
      split
      · split
        · cases parsed : Header.parse state.limits (bytes.push byte) with
          | error error => exact base
          | ok header =>
            dsimp only
            cases admitted : state.acceptHeader header with
            | error error => exact base
            | ok value =>
              cases value
              dsimp only
              split
              · exact ledger_commit property state base append header ByteArray.empty
              · exact base
        · exact base
      · exact base
    | payload header bytes =>
      dsimp only
      split
      · split
        · exact ledger_commit property state base append header (bytes.push byte)
        · exact base
      · exact base

structure Indexed (frames : List Frame) (keys : Std.TreeSet Nat compare) : Prop where
  uniqueNormal : frames.Pairwise (fun first second => first.header.tag ≠ .blob →
    first.header.tag ≠ second.header.tag)
  uniqueBlob : frames.Pairwise (fun first second => first.header.tag = .blob →
    second.header.tag = .blob → first.blobKey ≠ second.blobKey)
  recorded : ∀ frame ∈ frames, frame.header.tag = .blob → fromLittleEndian frame.blobKey ∈ keys
  keyBound : ∀ key ∈ keys, key < 256 ^ 64

theorem indexed_empty : Indexed [] ∅ := by
  constructor <;> simp

theorem indexed_append (state : State) (base : Indexed state.framesRev state.blobKeys)
    (header : Header) (payload : ByteArray) (terminal : Option Terminal)
    (accepted : state.acceptHeader header = .ok ())
    (blobAccepted : state.acceptBlob header payload = .ok ()) :
    Indexed (state.append header payload terminal).framesRev
      (state.append header payload terminal).blobKeys := by
  have admission := acceptHeader_fields state header accepted
  constructor
  · apply List.pairwise_cons.mpr
    refine ⟨?_, base.uniqueNormal⟩
    intro old member normal equal
    have unseen := (admission.2.2 normal).2
    have absent := List.any_eq_false.mp unseen old member
    apply absent
    exact (tag_beq old.header.tag header.tag).mpr equal.symm
  · apply List.pairwise_cons.mpr
    refine ⟨?_, base.uniqueBlob⟩
    intro old member blob oldBlob equal
    have noKey := (acceptBlob_fields state header payload blobAccepted blob).2.2
    have recorded := base.recorded old member oldBlob
    have keyEqual : fromLittleEndian (Frame.mk header payload).blobKey = fromLittleEndian old.blobKey :=
      congrArg fromLittleEndian equal
    rw [← keyEqual] at recorded
    have contains := Std.TreeSet.mem_iff_contains.mp recorded
    simp only [State.seenBlob, Frame.blobKey] at noKey contains
    rw [noKey] at contains
    contradiction
  · intro frame member blob
    simp only [State.append, List.mem_cons] at member
    rcases member with rfl | old
    · have newBlob : header.tag = .blob := blob
      simp only [State.append, newBlob, ite_true]
      exact Std.TreeSet.mem_insert_self
    · by_cases newBlob : header.tag = .blob
      · simp only [State.append, newBlob, ite_true, Std.TreeSet.mem_insert]
        exact Or.inr (base.recorded frame old blob)
      · simpa only [State.append, newBlob, ite_false] using base.recorded frame old blob
  · intro key member
    by_cases blob : header.tag = .blob
    · simp only [State.append, blob, ite_true, Std.TreeSet.mem_insert] at member
      rcases member with equal | old
      · have equalKey : fromLittleEndian (Frame.mk header payload).blobKey = key := by simpa using equal
        rw [← equalKey]
        have bytes := (acceptBlob_fields state header payload blobAccepted blob).1
        have bound := fromLittleEndian_bound (Frame.mk header payload).blobKey
        simpa only [Frame.blobKey, bytes] using bound
      · exact base.keyBound key old
    · exact base.keyBound key (by simpa only [State.append, blob, ite_false] using member)

theorem indexed_byte (state : State) (base : Indexed state.framesRev state.blobKeys) (byte : UInt8) :
    Indexed (state.byte byte).framesRev (state.byte byte).blobKeys := by
  apply ledger_byte Indexed state base
  intro header payload terminal _ admitted _ blob
  exact indexed_append state base header payload terminal admitted blob

theorem indexed_bytes (state : State) (base : Indexed state.framesRev state.blobKeys) (bytes : List UInt8) :
    Indexed (state.bytes bytes).framesRev (state.bytes bytes).blobKeys := by
  induction bytes generalizing state with
  | nil => exact base
  | cons byte bytes ih => exact ih (state.byte byte) (indexed_byte state base byte)

theorem indexed_step (state : State) (base : Indexed state.framesRev state.blobKeys) (event : Event) :
    Indexed (state.step event).framesRev (state.step event).blobKeys := by
  unfold State.step
  split
  · exact base
  · cases event with
    | eof => exact base
    | data bytes =>
      dsimp only
      split
      · exact base
      · split
        · exact base
        · exact indexed_bytes state base bytes.data.toList

theorem indexed_run (state : State) (base : Indexed state.framesRev state.blobKeys) (events : List Event) :
    Indexed (state.run events).framesRev (state.run events).blobKeys := by
  induction events generalizing state with
  | nil => exact base
  | cons event events ih => exact ih (state.step event) (indexed_step state base event)

end LeanCage.Host.Transport
