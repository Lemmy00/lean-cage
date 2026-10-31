import LeanCageM3

set_option autoImplicit false
-- §AR-m4-public.bytes: Exact byte windows and arbitrary-width little-endian word values.
namespace LeanCageM4.PublicCodec
open LeanCageM3

def word (width n : Nat) : List UInt8 :=
  match width with
  | 0 => []
  | width + 1 => UInt8.ofNat n :: word width (n / 256)
termination_by structural width

def value : List UInt8 → Nat
  | [] => 0
  | byte :: rest => byte.toNat + 256 * value rest

theorem word_length (width n : Nat) : (word width n).length = width := by
  induction width generalizing n with
  | zero => rfl
  | succ width ih => simp [word, ih]

theorem value_word (width n : Nat) : value (word width n) = n % 256^width := by
  induction width generalizing n with
  | zero => simp [word, value, Nat.mod_one]
  | succ width ih =>
    simp only [word, value, ih, Nat.pow_succ]
    rw [Nat.mul_comm (256^width) 256, Nat.mod_mul]
    rfl

theorem value_append (left right : List UInt8) :
    value (left ++ right) = value left + 256^left.length * value right := by
  induction left with
  | nil => simp [value]
  | cons byte rest ih =>
    simp only [List.cons_append, value, ih, List.length_cons, Nat.pow_succ]
    simp only [Nat.mul_add, Nat.add_assoc, Nat.mul_assoc]
    rw [Nat.mul_left_comm 256 (256^rest.length)]

theorem value_singleton (byte : UInt8) : value [byte] = byte.toNat := by
  simp [value]

theorem base_power (width : Nat) : 256^width = 2^(8*width) := by
  rw [Nat.pow_mul]

theorem little_range (bytes : ByteArray) (offset width : Nat) :
    little bytes offset width =
      value ((List.range width).map fun i => bytes[offset+i]?.getD 0) := by
  induction width with
  | zero => simp [little, value]
  | succ width ih =>
    have step : little bytes offset (width+1) = little bytes offset width +
        (bytes[offset+width]?.getD 0).toNat * 2^(8*width) := by
      simp only [little, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [step, ih, List.range_succ, List.map_append, value_append]
    simp [value, List.length_map, base_power, Nat.mul_comm]

theorem range_lookup (xs : List UInt8) :
    (List.range xs.length).map (fun i => xs[i]?.getD 0) = xs := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [List.getElem?_eq_getElem hj]

theorem bytes_get (xs : List UInt8) (i : Nat) :
    (ByteArray.mk xs.toArray)[i]? = xs[i]? := by
  simp only [getElem?_def, ByteArray.size, List.size_toArray]
  split <;> simp_all [ByteArray.getElem_eq_getElem_data]

theorem bytes_window (front payload suffix : List UInt8) :
    little (ByteArray.mk (front ++ payload ++ suffix).toArray) front.length payload.length =
      value payload := by
  rw [little_range]
  have same : (List.range payload.length).map
      (fun i => (ByteArray.mk (front ++ payload ++ suffix).toArray)[front.length+i]?.getD 0) =
      (List.range payload.length).map (fun i => payload[i]?.getD 0) := by
    apply List.map_congr_left
    intro i hi
    have bound : i < payload.length := List.mem_range.mp hi
    rw [bytes_get, List.append_assoc, List.getElem?_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left]
    rw [List.getElem?_append_left bound]
  rw [same, range_lookup]

theorem little_word (front suffix : List UInt8) (width n : Nat) :
    little (ByteArray.mk (front ++ word width n ++ suffix).toArray) front.length width =
      n % 2^(8*width) := by
  have h := bytes_window front (word width n) suffix
  simpa only [word_length, value_word, base_power] using h

theorem little_after (front rest : List UInt8) (offset width : Nat)
    (past : front.length ≤ offset) :
    little (ByteArray.mk (front ++ rest).toArray) offset width =
      little (ByteArray.mk rest.toArray) (offset-front.length) width := by
  rw [little_range, little_range]
  congr 1
  apply List.map_congr_left
  intro i _
  rw [bytes_get, bytes_get, List.getElem?_append_right (by omega)]
  congr 2
  omega

theorem little_head_word (width n : Nat) (rest : List UInt8) :
    little (ByteArray.mk (word width n ++ rest).toArray) 0 width = n % 2^(8*width) := by
  simpa using little_word [] rest width n

theorem extract_window (front payload suffix : List UInt8) :
    (ByteArray.mk (front ++ payload ++ suffix).toArray).extract
      front.length (front.length+payload.length) = ByteArray.mk payload.toArray := by
  apply ByteArray.ext
  simp only [ByteArray.data_extract, List.extract_toArray]
  simp [List.extract_eq_take_drop, List.append_assoc]

end LeanCageM4.PublicCodec


-- §AR-m4-public.parser: The elaborator returns only the existing live parser constant.
open Lean Elab Term Parser.Tactic
elab "m3Parser" : term => return mkConst (mkPrivateNameCore `LeanCageM3.Results `LeanCageM3.parseResult)

macro "unfold_m3_parser" : tactic => `(tactic| unfold $(mkIdent (mkPrivateNameCore `LeanCageM3.Results `LeanCageM3.parseResult)))

macro "unfold_m3_parser_at" h:ident : tactic => do
  let loc ← `(locationHyp| $h:ident)
  `(tactic| unfold $(mkIdent (mkPrivateNameCore `LeanCageM3.Results `LeanCageM3.parseResult)) at $loc:locationHyp)

set_option autoImplicit false
namespace LeanCageM4.PublicWire
open LeanCageM3

-- §AR-m4-public.parser: A transparent proof view matches the live parser by kernel equality.
def headerBad (bytes : ByteArray) : Bool :=
  bytes.size != 160 || bytes.extract 0 4 != "LC3R".toUTF8 ||
  little bytes 4 2 != 1 || little bytes 16 8 != 0 || little bytes 24 4 != 128 ||
  little bytes 28 4 != 0 || little bytes 156 4 != 0

def fields (bytes : ByteArray) (entry : Entry) : Result :=
  ⟨little bytes 6 2, little bytes 32 4, little bytes 36 4, entry,
    little bytes 44 4 == 1, little bytes 48 4, little bytes 52 4, little bytes 8 8,
    little bytes 56 8, little bytes 64 8, little bytes 72 8, little bytes 80 8, little bytes 88 8,
    little bytes 96 4, little bytes 100 4, bytes.extract 104 136,
    little bytes 136 8, little bytes 144 8, little bytes 152 4⟩

def entryWord : Entry → Nat
  | .no => 0
  | .yes => 1
  | .unknown => 2

def parserView : ByteArray → Except String Result := m3Parser

theorem live_decode_view (bytes : ByteArray) :
    decodeResult bytes = (parserView bytes).bind validateResult := rfl

theorem parserView_complete (bytes : ByteArray) (entry : Entry)
    (header : headerBad bytes = false) (entryCode : little bytes 40 4 = entryWord entry)
    (cleanup : little bytes 44 4 ≤ 1) : parserView bytes = .ok (fields bytes entry) := by
  unfold headerBad at header
  unfold parserView
  unfold_m3_parser
  simp only [header, Bool.false_eq_true, ite_false]
  cases entry <;> simp [entryWord, entryCode, Nat.not_lt.mpr cleanup, fields] <;> rfl

theorem parserView_sound (bytes : ByteArray) (r : Result)
    (accepted : parserView bytes = .ok r) :
    headerBad bytes = false ∧ ∃ entry, little bytes 40 4 = entryWord entry ∧
      little bytes 44 4 ≤ 1 ∧ r = fields bytes entry := by
  cases headerOK : headerBad bytes with
  | true =>
    unfold headerBad at headerOK
    unfold parserView at accepted
    unfold_m3_parser_at accepted
    simp only [headerOK, ite_true] at accepted
    contradiction
  | false =>
    refine ⟨rfl, ?_⟩
    unfold headerBad at headerOK
    unfold parserView at accepted
    unfold_m3_parser_at accepted
    simp only [headerOK, Bool.false_eq_true, ite_false] at accepted
    split at accepted
    · rename_i n entryCode
      by_cases bad : little bytes 44 4 > 1
      · simp only [bad, ite_true] at accepted
        contradiction
      · simp only [bad, ite_false] at accepted
        have same : fields bytes .no = r := Except.ok.inj accepted
        exact ⟨.no, entryCode, Nat.le_of_not_gt bad, same.symm⟩
    · rename_i n entryCode
      by_cases bad : little bytes 44 4 > 1
      · simp only [bad, ite_true] at accepted
        contradiction
      · simp only [bad, ite_false] at accepted
        have same : fields bytes .yes = r := Except.ok.inj accepted
        exact ⟨.yes, entryCode, Nat.le_of_not_gt bad, same.symm⟩
    · rename_i n entryCode
      by_cases bad : little bytes 44 4 > 1
      · simp only [bad, ite_true] at accepted
        contradiction
      · simp only [bad, ite_false] at accepted
        have same : fields bytes .unknown = r := Except.ok.inj accepted
        exact ⟨.unknown, entryCode, Nat.le_of_not_gt bad, same.symm⟩
    · contradiction

theorem parserView_iff (bytes : ByteArray) (r : Result) :
    parserView bytes = .ok r ↔
    headerBad bytes = false ∧ ∃ entry, little bytes 40 4 = entryWord entry ∧
      little bytes 44 4 ≤ 1 ∧ r = fields bytes entry := by
  constructor
  · exact parserView_sound bytes r
  · rintro ⟨header, entry, entryCode, cleanup, rfl⟩
    exact parserView_complete bytes entry header entryCode cleanup

theorem decodeResult_iff (bytes : ByteArray) (r : Result) :
    decodeResult bytes = .ok r ↔
    headerBad bytes = false ∧ ∃ entry, little bytes 40 4 = entryWord entry ∧
      little bytes 44 4 ≤ 1 ∧ r = fields bytes entry ∧ resultValid r = true := by
  rw [live_decode_view]
  constructor
  · intro accepted
    cases parsed : parserView bytes with
    | error message => rw [parsed] at accepted; contradiction
    | ok value =>
      rw [parsed] at accepted
      change validateResult value = .ok r at accepted
      unfold validateResult at accepted
      split at accepted
      · rename_i valid
        cases accepted
        obtain ⟨header, entry, entryCode, cleanup, same⟩ := parserView_sound bytes r parsed
        exact ⟨header, entry, entryCode, cleanup, same, valid⟩
      · contradiction
  · rintro ⟨header, entry, entryCode, cleanup, rfl, valid⟩
    rw [parserView_complete bytes entry header entryCode cleanup]
    change validateResult (fields bytes entry) = .ok (fields bytes entry)
    simp [validateResult, valid]

theorem little_succ (bytes : ByteArray) (offset width : Nat) :
    little bytes offset (width + 1) = little bytes offset width +
      (bytes[offset + width]?.getD 0).toNat * 2 ^ (8 * width) := by
  simp only [little, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem little_bounded (bytes : ByteArray) (offset width : Nat) :
    little bytes offset width < 2 ^ (8 * width) := by
  induction width with
  | zero => simp [little]
  | succ width ih =>
    rw [little_succ]
    have byteBound := (bytes[offset + width]?.getD 0).toNat_lt_size
    have mulBound := Nat.mul_le_mul_right (2 ^ (8 * width)) (Nat.le_pred_of_lt byteBound)
    have power : 2 ^ (8 * (width + 1)) = 256 * 2 ^ (8 * width) := by
      rw [Nat.mul_add, Nat.mul_one, Nat.pow_add]
      simp only [show 2 ^ 8 = 256 from rfl, Nat.mul_comm]
    rw [power]
    change (bytes[offset + width]?.getD 0).toNat * 2 ^ (8 * width) ≤ 255 * 2 ^ (8 * width) at mulBound
    omega

theorem byteArray_bne_false (a b : ByteArray) : (a != b) = false ↔ a = b := by
  change (!(a.data == b.data)) = false ↔ a = b
  simp [ByteArray.ext_iff]

theorem headerBad_iff (bytes : ByteArray) :
    headerBad bytes = false ↔ bytes.size = 160 ∧ bytes.extract 0 4 = "LC3R".toUTF8 ∧
      little bytes 4 2 = 1 ∧ little bytes 16 8 = 0 ∧ little bytes 24 4 = 128 ∧
      little bytes 28 4 = 0 ∧ little bytes 156 4 = 0 := by
  simp [headerBad, byteArray_bne_false, and_assoc]

def Widths (r : Result) : Prop :=
  r.kind < 2^16 ∧ r.stage < 2^32 ∧ r.detail < 2^32 ∧
  r.triggers < 2^32 ∧ r.uid < 2^32 ∧ r.run < 2^64 ∧ r.cpu < 2^64 ∧ r.peak < 2^64 ∧
  r.stdoutBytes < 2^64 ∧ r.stderrBytes < 2^64 ∧ r.elapsed < 2^64 ∧
  r.exportState < 2^32 ∧ r.omitted < 2^32 ∧ r.oomKills < 2^64 ∧
  r.taskDenials < 2^64 ∧ r.exportError < 2^32

theorem fields_widths (bytes : ByteArray) (entry : Entry) : Widths (fields bytes entry) := by
  simp only [Widths, fields]
  exact ⟨little_bounded bytes 6 2, little_bounded bytes 32 4, little_bounded bytes 36 4,
    little_bounded bytes 48 4, little_bounded bytes 52 4, little_bounded bytes 8 8,
    little_bounded bytes 56 8, little_bounded bytes 64 8, little_bounded bytes 72 8,
    little_bounded bytes 80 8, little_bounded bytes 88 8, little_bounded bytes 96 4,
    little_bounded bytes 100 4, little_bounded bytes 136 8, little_bounded bytes 144 8,
    little_bounded bytes 152 4⟩

theorem accepted_widths (bytes : ByteArray) (r : Result)
    (accepted : decodeResult bytes = .ok r) : Widths r := by
  obtain ⟨_, entry, _, _, rfl, _⟩ := (decodeResult_iff bytes r).mp accepted
  exact fields_widths bytes entry

theorem accepted_header (bytes : ByteArray) (r : Result)
    (accepted : decodeResult bytes = .ok r) :
    bytes.size = 160 ∧ bytes.extract 0 4 = "LC3R".toUTF8 ∧
      little bytes 4 2 = 1 ∧ little bytes 16 8 = 0 ∧ little bytes 24 4 = 128 ∧
      little bytes 28 4 = 0 ∧ little bytes 156 4 = 0 :=
  (headerBad_iff bytes).mp ((decodeResult_iff bytes r).mp accepted).1

end LeanCageM4.PublicWire

-- §AR-m4-public.bytes: Proof-side encoding, complete fields and live decoder round trips.
namespace LeanCageM4.PublicEncode
open LeanCageM3 LeanCageM4.PublicCodec LeanCageM4.PublicWire

def frameBytes (r : Result) : List UInt8 :=
  [76, 67, 51, 82] ++ word 2 1 ++ word 2 r.kind ++ word 8 r.run ++ word 8 0 ++
  word 4 128 ++ word 4 0 ++ word 4 r.stage ++ word 4 r.detail ++ word 4 (entryWord r.entry) ++
  word 4 (if r.clean then 1 else 0) ++ word 4 r.triggers ++ word 4 r.uid ++
  word 8 r.cpu ++ word 8 r.peak ++ word 8 r.stdoutBytes ++ word 8 r.stderrBytes ++
  word 8 r.elapsed ++ word 4 r.exportState ++ word 4 r.omitted ++ r.exportDigest.data.toList ++
  word 8 r.oomKills ++ word 8 r.taskDenials ++ word 4 r.exportError ++ word 4 0

def encodeResult (r : Result) : ByteArray := ByteArray.mk (frameBytes r).toArray

theorem frame_length (r : Result) : (encodeResult r).size = 128 + r.exportDigest.size := by
  delta encodeResult frameBytes
  simp only [ByteArray.size, List.size_toArray, List.length_append,
    word_length, List.length_cons, List.length_nil, Array.length_toList]
  cases r
  dsimp only
  omega

theorem frame_version (r : Result) :
    little (encodeResult r) 4 2 = 1 % 2^16 := by
  let front : List UInt8 := [76, 67, 51, 82]
  let rest : List UInt8 := word 2 (r.kind) ++ word 8 (r.run) ++ word 8 (0) ++ word 4 (128) ++
    word 4 (0) ++ word 4 (r.stage) ++ word 4 (r.detail) ++ word 4 (entryWord r.entry) ++
    word 4 ((if r.clean then 1 else 0)) ++ word 4 (r.triggers) ++ word 4 (r.uid) ++ word 8 (r.cpu) ++
    word 8 (r.peak) ++ word 8 (r.stdoutBytes) ++ word 8 (r.stderrBytes) ++ word 8 (r.elapsed) ++
    word 4 (r.exportState) ++ word 4 (r.omitted) ++ r.exportDigest.data.toList ++
    word 8 (r.oomKills) ++ word 8 (r.taskDenials) ++ word 4 (r.exportError) ++ word 4 (0)
  have size : front.length = 4 := by
    simp only [front, List.length_cons, List.length_nil]
  have h := little_word front rest 2 (1)
  rw [size] at h
  delta encodeResult frameBytes
  dsimp only [front, rest] at h
  simpa only [List.append_assoc, List.append_nil] using h

theorem frame_kind (r : Result) :
    little (encodeResult r) 6 2 = r.kind % 2^16 := by
  let front : List UInt8 := [76, 67, 51, 82] ++ word 2 (1)
  let rest : List UInt8 := word 8 (r.run) ++ word 8 (0) ++ word 4 (128) ++ word 4 (0) ++
    word 4 (r.stage) ++ word 4 (r.detail) ++ word 4 (entryWord r.entry) ++
    word 4 ((if r.clean then 1 else 0)) ++ word 4 (r.triggers) ++ word 4 (r.uid) ++ word 8 (r.cpu) ++
    word 8 (r.peak) ++ word 8 (r.stdoutBytes) ++ word 8 (r.stderrBytes) ++ word 8 (r.elapsed) ++
    word 4 (r.exportState) ++ word 4 (r.omitted) ++ r.exportDigest.data.toList ++
    word 8 (r.oomKills) ++ word 8 (r.taskDenials) ++ word 4 (r.exportError) ++ word 4 (0)
  have size : front.length = 6 := by
    simp only [front, List.length_append, word_length, List.length_cons, List.length_nil]
  have h := little_word front rest 2 (r.kind)
  rw [size] at h
  delta encodeResult frameBytes
  dsimp only [front, rest] at h
  simpa only [List.append_assoc, List.append_nil] using h

theorem frame_run (r : Result) :
    little (encodeResult r) 8 8 = r.run % 2^64 := by
  let front : List UInt8 := [76, 67, 51, 82] ++ word 2 (1) ++ word 2 (r.kind)
  let rest : List UInt8 := word 8 (0) ++ word 4 (128) ++ word 4 (0) ++ word 4 (r.stage) ++
    word 4 (r.detail) ++ word 4 (entryWord r.entry) ++ word 4 ((if r.clean then 1 else 0)) ++
    word 4 (r.triggers) ++ word 4 (r.uid) ++ word 8 (r.cpu) ++ word 8 (r.peak) ++
    word 8 (r.stdoutBytes) ++ word 8 (r.stderrBytes) ++ word 8 (r.elapsed) ++ word 4 (r.exportState) ++
    word 4 (r.omitted) ++ r.exportDigest.data.toList ++ word 8 (r.oomKills) ++
    word 8 (r.taskDenials) ++ word 4 (r.exportError) ++ word 4 (0)
  have size : front.length = 8 := by
    simp only [front, List.length_append, word_length, List.length_cons, List.length_nil]
  have h := little_word front rest 8 (r.run)
  rw [size] at h
  delta encodeResult frameBytes
  dsimp only [front, rest] at h
  simpa only [List.append_assoc, List.append_nil] using h

theorem frame_sequence (r : Result) :
    little (encodeResult r) 16 8 = 0 % 2^64 := by
  let front : List UInt8 := [76, 67, 51, 82] ++ word 2 (1) ++ word 2 (r.kind) ++ word 8 (r.run)
  let rest : List UInt8 := word 4 (128) ++ word 4 (0) ++ word 4 (r.stage) ++ word 4 (r.detail) ++
    word 4 (entryWord r.entry) ++ word 4 ((if r.clean then 1 else 0)) ++ word 4 (r.triggers) ++
    word 4 (r.uid) ++ word 8 (r.cpu) ++ word 8 (r.peak) ++ word 8 (r.stdoutBytes) ++
    word 8 (r.stderrBytes) ++ word 8 (r.elapsed) ++ word 4 (r.exportState) ++ word 4 (r.omitted) ++
    r.exportDigest.data.toList ++ word 8 (r.oomKills) ++ word 8 (r.taskDenials) ++
    word 4 (r.exportError) ++ word 4 (0)
  have size : front.length = 16 := by
    simp only [front, List.length_append, word_length, List.length_cons, List.length_nil]
  have h := little_word front rest 8 (0)
  rw [size] at h
  delta encodeResult frameBytes
  dsimp only [front, rest] at h
  simpa only [List.append_assoc, List.append_nil] using h

theorem frame_payload_length (r : Result) :
    little (encodeResult r) 24 4 = 128 % 2^32 := by
  let front : List UInt8 := [76, 67, 51, 82] ++ word 2 (1) ++ word 2 (r.kind) ++ word 8 (r.run) ++
    word 8 (0)
  let rest : List UInt8 := word 4 (0) ++ word 4 (r.stage) ++ word 4 (r.detail) ++
    word 4 (entryWord r.entry) ++ word 4 ((if r.clean then 1 else 0)) ++ word 4 (r.triggers) ++
    word 4 (r.uid) ++ word 8 (r.cpu) ++ word 8 (r.peak) ++ word 8 (r.stdoutBytes) ++
    word 8 (r.stderrBytes) ++ word 8 (r.elapsed) ++ word 4 (r.exportState) ++ word 4 (r.omitted) ++
    r.exportDigest.data.toList ++ word 8 (r.oomKills) ++ word 8 (r.taskDenials) ++
    word 4 (r.exportError) ++ word 4 (0)
  have size : front.length = 24 := by
    simp only [front, List.length_append, word_length, List.length_cons, List.length_nil]
  have h := little_word front rest 4 (128)
  rw [size] at h
  delta encodeResult frameBytes
  dsimp only [front, rest] at h
  simpa only [List.append_assoc, List.append_nil] using h

theorem frame_reserved_header (r : Result) :
    little (encodeResult r) 28 4 = 0 % 2^32 := by
  let front : List UInt8 := [76, 67, 51, 82] ++ word 2 (1) ++ word 2 (r.kind) ++ word 8 (r.run) ++
    word 8 (0) ++ word 4 (128)
  let rest : List UInt8 := word 4 (r.stage) ++ word 4 (r.detail) ++ word 4 (entryWord r.entry) ++
    word 4 ((if r.clean then 1 else 0)) ++ word 4 (r.triggers) ++ word 4 (r.uid) ++ word 8 (r.cpu) ++
    word 8 (r.peak) ++ word 8 (r.stdoutBytes) ++ word 8 (r.stderrBytes) ++ word 8 (r.elapsed) ++
    word 4 (r.exportState) ++ word 4 (r.omitted) ++ r.exportDigest.data.toList ++
    word 8 (r.oomKills) ++ word 8 (r.taskDenials) ++ word 4 (r.exportError) ++ word 4 (0)
  have size : front.length = 28 := by
    simp only [front, List.length_append, word_length, List.length_cons, List.length_nil]
  have h := little_word front rest 4 (0)
  rw [size] at h
  delta encodeResult frameBytes
  dsimp only [front, rest] at h
  simpa only [List.append_assoc, List.append_nil] using h

theorem frame_stage (r : Result) :
    little (encodeResult r) 32 4 = r.stage % 2^32 := by
  let front : List UInt8 := [76, 67, 51, 82] ++ word 2 (1) ++ word 2 (r.kind) ++ word 8 (r.run) ++
    word 8 (0) ++ word 4 (128) ++ word 4 (0)
  let rest : List UInt8 := word 4 (r.detail) ++ word 4 (entryWord r.entry) ++
    word 4 ((if r.clean then 1 else 0)) ++ word 4 (r.triggers) ++ word 4 (r.uid) ++ word 8 (r.cpu) ++
    word 8 (r.peak) ++ word 8 (r.stdoutBytes) ++ word 8 (r.stderrBytes) ++ word 8 (r.elapsed) ++
    word 4 (r.exportState) ++ word 4 (r.omitted) ++ r.exportDigest.data.toList ++
    word 8 (r.oomKills) ++ word 8 (r.taskDenials) ++ word 4 (r.exportError) ++ word 4 (0)
  have size : front.length = 32 := by
    simp only [front, List.length_append, word_length, List.length_cons, List.length_nil]
  have h := little_word front rest 4 (r.stage)
  rw [size] at h
  delta encodeResult frameBytes
  dsimp only [front, rest] at h
  simpa only [List.append_assoc, List.append_nil] using h

theorem frame_detail (r : Result) :
    little (encodeResult r) 36 4 = r.detail % 2^32 := by
  let front : List UInt8 := [76, 67, 51, 82] ++ word 2 (1) ++ word 2 (r.kind) ++ word 8 (r.run) ++
    word 8 (0) ++ word 4 (128) ++ word 4 (0) ++ word 4 (r.stage)
  let rest : List UInt8 := word 4 (entryWord r.entry) ++ word 4 ((if r.clean then 1 else 0)) ++
    word 4 (r.triggers) ++ word 4 (r.uid) ++ word 8 (r.cpu) ++ word 8 (r.peak) ++
    word 8 (r.stdoutBytes) ++ word 8 (r.stderrBytes) ++ word 8 (r.elapsed) ++ word 4 (r.exportState) ++
    word 4 (r.omitted) ++ r.exportDigest.data.toList ++ word 8 (r.oomKills) ++
    word 8 (r.taskDenials) ++ word 4 (r.exportError) ++ word 4 (0)
  have size : front.length = 36 := by
    simp only [front, List.length_append, word_length, List.length_cons, List.length_nil]
  have h := little_word front rest 4 (r.detail)
  rw [size] at h
  delta encodeResult frameBytes
  dsimp only [front, rest] at h
  simpa only [List.append_assoc, List.append_nil] using h

theorem frame_entry (r : Result) :
    little (encodeResult r) 40 4 = entryWord r.entry % 2^32 := by
  let front : List UInt8 := [76, 67, 51, 82] ++ word 2 (1) ++ word 2 (r.kind) ++ word 8 (r.run) ++
    word 8 (0) ++ word 4 (128) ++ word 4 (0) ++ word 4 (r.stage) ++ word 4 (r.detail)
  let rest : List UInt8 := word 4 ((if r.clean then 1 else 0)) ++ word 4 (r.triggers) ++
    word 4 (r.uid) ++ word 8 (r.cpu) ++ word 8 (r.peak) ++ word 8 (r.stdoutBytes) ++
    word 8 (r.stderrBytes) ++ word 8 (r.elapsed) ++ word 4 (r.exportState) ++ word 4 (r.omitted) ++
    r.exportDigest.data.toList ++ word 8 (r.oomKills) ++ word 8 (r.taskDenials) ++
    word 4 (r.exportError) ++ word 4 (0)
  have size : front.length = 40 := by
    simp only [front, List.length_append, word_length, List.length_cons, List.length_nil]
  have h := little_word front rest 4 (entryWord r.entry)
  rw [size] at h
  delta encodeResult frameBytes
  dsimp only [front, rest] at h
  simpa only [List.append_assoc, List.append_nil] using h

theorem frame_cleanup (r : Result) :
    little (encodeResult r) 44 4 = (if r.clean then 1 else 0) % 2^32 := by
  let front : List UInt8 := [76, 67, 51, 82] ++ word 2 (1) ++ word 2 (r.kind) ++ word 8 (r.run) ++
    word 8 (0) ++ word 4 (128) ++ word 4 (0) ++ word 4 (r.stage) ++ word 4 (r.detail) ++
    word 4 (entryWord r.entry)
  let rest : List UInt8 := word 4 (r.triggers) ++ word 4 (r.uid) ++ word 8 (r.cpu) ++
    word 8 (r.peak) ++ word 8 (r.stdoutBytes) ++ word 8 (r.stderrBytes) ++ word 8 (r.elapsed) ++
    word 4 (r.exportState) ++ word 4 (r.omitted) ++ r.exportDigest.data.toList ++
    word 8 (r.oomKills) ++ word 8 (r.taskDenials) ++ word 4 (r.exportError) ++ word 4 (0)
  have size : front.length = 44 := by
    simp only [front, List.length_append, word_length, List.length_cons, List.length_nil]
  have h := little_word front rest 4 ((if r.clean then 1 else 0))
  rw [size] at h
  delta encodeResult frameBytes
  dsimp only [front, rest] at h
  simpa only [List.append_assoc, List.append_nil] using h

theorem frame_triggers (r : Result) :
    little (encodeResult r) 48 4 = r.triggers % 2^32 := by
  let front : List UInt8 := [76, 67, 51, 82] ++ word 2 (1) ++ word 2 (r.kind) ++ word 8 (r.run) ++
    word 8 (0) ++ word 4 (128) ++ word 4 (0) ++ word 4 (r.stage) ++ word 4 (r.detail) ++
    word 4 (entryWord r.entry) ++ word 4 ((if r.clean then 1 else 0))
  let rest : List UInt8 := word 4 (r.uid) ++ word 8 (r.cpu) ++ word 8 (r.peak) ++
    word 8 (r.stdoutBytes) ++ word 8 (r.stderrBytes) ++ word 8 (r.elapsed) ++ word 4 (r.exportState) ++
    word 4 (r.omitted) ++ r.exportDigest.data.toList ++ word 8 (r.oomKills) ++
    word 8 (r.taskDenials) ++ word 4 (r.exportError) ++ word 4 (0)
  have size : front.length = 48 := by
    simp only [front, List.length_append, word_length, List.length_cons, List.length_nil]
  have h := little_word front rest 4 (r.triggers)
  rw [size] at h
  delta encodeResult frameBytes
  dsimp only [front, rest] at h
  simpa only [List.append_assoc, List.append_nil] using h

theorem frame_uid (r : Result) :
    little (encodeResult r) 52 4 = r.uid % 2^32 := by
  let front : List UInt8 := [76, 67, 51, 82] ++ word 2 (1) ++ word 2 (r.kind) ++ word 8 (r.run) ++
    word 8 (0) ++ word 4 (128) ++ word 4 (0) ++ word 4 (r.stage) ++ word 4 (r.detail) ++
    word 4 (entryWord r.entry) ++ word 4 ((if r.clean then 1 else 0)) ++ word 4 (r.triggers)
  let rest : List UInt8 := word 8 (r.cpu) ++ word 8 (r.peak) ++ word 8 (r.stdoutBytes) ++
    word 8 (r.stderrBytes) ++ word 8 (r.elapsed) ++ word 4 (r.exportState) ++ word 4 (r.omitted) ++
    r.exportDigest.data.toList ++ word 8 (r.oomKills) ++ word 8 (r.taskDenials) ++
    word 4 (r.exportError) ++ word 4 (0)
  have size : front.length = 52 := by
    simp only [front, List.length_append, word_length, List.length_cons, List.length_nil]
  have h := little_word front rest 4 (r.uid)
  rw [size] at h
  delta encodeResult frameBytes
  dsimp only [front, rest] at h
  simpa only [List.append_assoc, List.append_nil] using h

theorem frame_cpu (r : Result) :
    little (encodeResult r) 56 8 = r.cpu % 2^64 := by
  let front : List UInt8 := [76, 67, 51, 82] ++ word 2 (1) ++ word 2 (r.kind) ++ word 8 (r.run) ++
    word 8 (0) ++ word 4 (128) ++ word 4 (0) ++ word 4 (r.stage) ++ word 4 (r.detail) ++
    word 4 (entryWord r.entry) ++ word 4 ((if r.clean then 1 else 0)) ++ word 4 (r.triggers) ++
    word 4 (r.uid)
  let rest : List UInt8 := word 8 (r.peak) ++ word 8 (r.stdoutBytes) ++ word 8 (r.stderrBytes) ++
    word 8 (r.elapsed) ++ word 4 (r.exportState) ++ word 4 (r.omitted) ++ r.exportDigest.data.toList ++
    word 8 (r.oomKills) ++ word 8 (r.taskDenials) ++ word 4 (r.exportError) ++ word 4 (0)
  have size : front.length = 56 := by
    simp only [front, List.length_append, word_length, List.length_cons, List.length_nil]
  have h := little_word front rest 8 (r.cpu)
  rw [size] at h
  delta encodeResult frameBytes
  dsimp only [front, rest] at h
  simpa only [List.append_assoc, List.append_nil] using h

theorem frame_peak (r : Result) :
    little (encodeResult r) 64 8 = r.peak % 2^64 := by
  let front : List UInt8 := [76, 67, 51, 82] ++ word 2 (1) ++ word 2 (r.kind) ++ word 8 (r.run) ++
    word 8 (0) ++ word 4 (128) ++ word 4 (0) ++ word 4 (r.stage) ++ word 4 (r.detail) ++
    word 4 (entryWord r.entry) ++ word 4 ((if r.clean then 1 else 0)) ++ word 4 (r.triggers) ++
    word 4 (r.uid) ++ word 8 (r.cpu)
  let rest : List UInt8 := word 8 (r.stdoutBytes) ++ word 8 (r.stderrBytes) ++ word 8 (r.elapsed) ++
    word 4 (r.exportState) ++ word 4 (r.omitted) ++ r.exportDigest.data.toList ++
    word 8 (r.oomKills) ++ word 8 (r.taskDenials) ++ word 4 (r.exportError) ++ word 4 (0)
  have size : front.length = 64 := by
    simp only [front, List.length_append, word_length, List.length_cons, List.length_nil]
  have h := little_word front rest 8 (r.peak)
  rw [size] at h
  delta encodeResult frameBytes
  dsimp only [front, rest] at h
  simpa only [List.append_assoc, List.append_nil] using h

theorem frame_stdout (r : Result) :
    little (encodeResult r) 72 8 = r.stdoutBytes % 2^64 := by
  let front : List UInt8 := [76, 67, 51, 82] ++ word 2 (1) ++ word 2 (r.kind) ++ word 8 (r.run) ++
    word 8 (0) ++ word 4 (128) ++ word 4 (0) ++ word 4 (r.stage) ++ word 4 (r.detail) ++
    word 4 (entryWord r.entry) ++ word 4 ((if r.clean then 1 else 0)) ++ word 4 (r.triggers) ++
    word 4 (r.uid) ++ word 8 (r.cpu) ++ word 8 (r.peak)
  let rest : List UInt8 := word 8 (r.stderrBytes) ++ word 8 (r.elapsed) ++ word 4 (r.exportState) ++
    word 4 (r.omitted) ++ r.exportDigest.data.toList ++ word 8 (r.oomKills) ++
    word 8 (r.taskDenials) ++ word 4 (r.exportError) ++ word 4 (0)
  have size : front.length = 72 := by
    simp only [front, List.length_append, word_length, List.length_cons, List.length_nil]
  have h := little_word front rest 8 (r.stdoutBytes)
  rw [size] at h
  delta encodeResult frameBytes
  dsimp only [front, rest] at h
  simpa only [List.append_assoc, List.append_nil] using h

theorem frame_stderr (r : Result) :
    little (encodeResult r) 80 8 = r.stderrBytes % 2^64 := by
  let front : List UInt8 := [76, 67, 51, 82] ++ word 2 (1) ++ word 2 (r.kind) ++ word 8 (r.run) ++
    word 8 (0) ++ word 4 (128) ++ word 4 (0) ++ word 4 (r.stage) ++ word 4 (r.detail) ++
    word 4 (entryWord r.entry) ++ word 4 ((if r.clean then 1 else 0)) ++ word 4 (r.triggers) ++
    word 4 (r.uid) ++ word 8 (r.cpu) ++ word 8 (r.peak) ++ word 8 (r.stdoutBytes)
  let rest : List UInt8 := word 8 (r.elapsed) ++ word 4 (r.exportState) ++ word 4 (r.omitted) ++
    r.exportDigest.data.toList ++ word 8 (r.oomKills) ++ word 8 (r.taskDenials) ++
    word 4 (r.exportError) ++ word 4 (0)
  have size : front.length = 80 := by
    simp only [front, List.length_append, word_length, List.length_cons, List.length_nil]
  have h := little_word front rest 8 (r.stderrBytes)
  rw [size] at h
  delta encodeResult frameBytes
  dsimp only [front, rest] at h
  simpa only [List.append_assoc, List.append_nil] using h

theorem frame_elapsed (r : Result) :
    little (encodeResult r) 88 8 = r.elapsed % 2^64 := by
  let front : List UInt8 := [76, 67, 51, 82] ++ word 2 (1) ++ word 2 (r.kind) ++ word 8 (r.run) ++
    word 8 (0) ++ word 4 (128) ++ word 4 (0) ++ word 4 (r.stage) ++ word 4 (r.detail) ++
    word 4 (entryWord r.entry) ++ word 4 ((if r.clean then 1 else 0)) ++ word 4 (r.triggers) ++
    word 4 (r.uid) ++ word 8 (r.cpu) ++ word 8 (r.peak) ++ word 8 (r.stdoutBytes) ++
    word 8 (r.stderrBytes)
  let rest : List UInt8 := word 4 (r.exportState) ++ word 4 (r.omitted) ++
    r.exportDigest.data.toList ++ word 8 (r.oomKills) ++ word 8 (r.taskDenials) ++
    word 4 (r.exportError) ++ word 4 (0)
  have size : front.length = 88 := by
    simp only [front, List.length_append, word_length, List.length_cons, List.length_nil]
  have h := little_word front rest 8 (r.elapsed)
  rw [size] at h
  delta encodeResult frameBytes
  dsimp only [front, rest] at h
  simpa only [List.append_assoc, List.append_nil] using h

theorem frame_export_state (r : Result) :
    little (encodeResult r) 96 4 = r.exportState % 2^32 := by
  let front : List UInt8 := [76, 67, 51, 82] ++ word 2 (1) ++ word 2 (r.kind) ++ word 8 (r.run) ++
    word 8 (0) ++ word 4 (128) ++ word 4 (0) ++ word 4 (r.stage) ++ word 4 (r.detail) ++
    word 4 (entryWord r.entry) ++ word 4 ((if r.clean then 1 else 0)) ++ word 4 (r.triggers) ++
    word 4 (r.uid) ++ word 8 (r.cpu) ++ word 8 (r.peak) ++ word 8 (r.stdoutBytes) ++
    word 8 (r.stderrBytes) ++ word 8 (r.elapsed)
  let rest : List UInt8 := word 4 (r.omitted) ++ r.exportDigest.data.toList ++ word 8 (r.oomKills) ++
    word 8 (r.taskDenials) ++ word 4 (r.exportError) ++ word 4 (0)
  have size : front.length = 96 := by
    simp only [front, List.length_append, word_length, List.length_cons, List.length_nil]
  have h := little_word front rest 4 (r.exportState)
  rw [size] at h
  delta encodeResult frameBytes
  dsimp only [front, rest] at h
  simpa only [List.append_assoc, List.append_nil] using h

theorem frame_omitted (r : Result) :
    little (encodeResult r) 100 4 = r.omitted % 2^32 := by
  let front : List UInt8 := [76, 67, 51, 82] ++ word 2 (1) ++ word 2 (r.kind) ++ word 8 (r.run) ++
    word 8 (0) ++ word 4 (128) ++ word 4 (0) ++ word 4 (r.stage) ++ word 4 (r.detail) ++
    word 4 (entryWord r.entry) ++ word 4 ((if r.clean then 1 else 0)) ++ word 4 (r.triggers) ++
    word 4 (r.uid) ++ word 8 (r.cpu) ++ word 8 (r.peak) ++ word 8 (r.stdoutBytes) ++
    word 8 (r.stderrBytes) ++ word 8 (r.elapsed) ++ word 4 (r.exportState)
  let rest : List UInt8 := r.exportDigest.data.toList ++ word 8 (r.oomKills) ++
    word 8 (r.taskDenials) ++ word 4 (r.exportError) ++ word 4 (0)
  have size : front.length = 100 := by
    simp only [front, List.length_append, word_length, List.length_cons, List.length_nil]
  have h := little_word front rest 4 (r.omitted)
  rw [size] at h
  delta encodeResult frameBytes
  dsimp only [front, rest] at h
  simpa only [List.append_assoc, List.append_nil] using h

theorem frame_oom (r : Result) (digestLength : r.exportDigest.size = 32) :
    little (encodeResult r) 136 8 = r.oomKills % 2^64 := by
  let front : List UInt8 := [76, 67, 51, 82] ++ word 2 (1) ++ word 2 (r.kind) ++ word 8 (r.run) ++
    word 8 (0) ++ word 4 (128) ++ word 4 (0) ++ word 4 (r.stage) ++ word 4 (r.detail) ++
    word 4 (entryWord r.entry) ++ word 4 ((if r.clean then 1 else 0)) ++ word 4 (r.triggers) ++
    word 4 (r.uid) ++ word 8 (r.cpu) ++ word 8 (r.peak) ++ word 8 (r.stdoutBytes) ++
    word 8 (r.stderrBytes) ++ word 8 (r.elapsed) ++ word 4 (r.exportState) ++ word 4 (r.omitted) ++
    r.exportDigest.data.toList
  let rest : List UInt8 := word 8 (r.taskDenials) ++ word 4 (r.exportError) ++ word 4 (0)
  have size : front.length = 136 := by
    simp only [front, List.length_append, word_length, List.length_cons, List.length_nil,
      Array.length_toList]
    cases r
    dsimp only [ByteArray.size] at digestLength ⊢
    omega
  have h := little_word front rest 8 (r.oomKills)
  rw [size] at h
  delta encodeResult frameBytes
  dsimp only [front, rest] at h
  simpa only [List.append_assoc, List.append_nil] using h

theorem frame_tasks (r : Result) (digestLength : r.exportDigest.size = 32) :
    little (encodeResult r) 144 8 = r.taskDenials % 2^64 := by
  let front : List UInt8 := [76, 67, 51, 82] ++ word 2 (1) ++ word 2 (r.kind) ++ word 8 (r.run) ++
    word 8 (0) ++ word 4 (128) ++ word 4 (0) ++ word 4 (r.stage) ++ word 4 (r.detail) ++
    word 4 (entryWord r.entry) ++ word 4 ((if r.clean then 1 else 0)) ++ word 4 (r.triggers) ++
    word 4 (r.uid) ++ word 8 (r.cpu) ++ word 8 (r.peak) ++ word 8 (r.stdoutBytes) ++
    word 8 (r.stderrBytes) ++ word 8 (r.elapsed) ++ word 4 (r.exportState) ++ word 4 (r.omitted) ++
    r.exportDigest.data.toList ++ word 8 (r.oomKills)
  let rest : List UInt8 := word 4 (r.exportError) ++ word 4 (0)
  have size : front.length = 144 := by
    simp only [front, List.length_append, word_length, List.length_cons, List.length_nil,
      Array.length_toList]
    cases r
    dsimp only [ByteArray.size] at digestLength ⊢
    omega
  have h := little_word front rest 8 (r.taskDenials)
  rw [size] at h
  delta encodeResult frameBytes
  dsimp only [front, rest] at h
  simpa only [List.append_assoc, List.append_nil] using h

theorem frame_export_error (r : Result) (digestLength : r.exportDigest.size = 32) :
    little (encodeResult r) 152 4 = r.exportError % 2^32 := by
  let front : List UInt8 := [76, 67, 51, 82] ++ word 2 (1) ++ word 2 (r.kind) ++ word 8 (r.run) ++
    word 8 (0) ++ word 4 (128) ++ word 4 (0) ++ word 4 (r.stage) ++ word 4 (r.detail) ++
    word 4 (entryWord r.entry) ++ word 4 ((if r.clean then 1 else 0)) ++ word 4 (r.triggers) ++
    word 4 (r.uid) ++ word 8 (r.cpu) ++ word 8 (r.peak) ++ word 8 (r.stdoutBytes) ++
    word 8 (r.stderrBytes) ++ word 8 (r.elapsed) ++ word 4 (r.exportState) ++ word 4 (r.omitted) ++
    r.exportDigest.data.toList ++ word 8 (r.oomKills) ++ word 8 (r.taskDenials)
  let rest : List UInt8 := word 4 (0)
  have size : front.length = 152 := by
    simp only [front, List.length_append, word_length, List.length_cons, List.length_nil,
      Array.length_toList]
    cases r
    dsimp only [ByteArray.size] at digestLength ⊢
    omega
  have h := little_word front rest 4 (r.exportError)
  rw [size] at h
  delta encodeResult frameBytes
  dsimp only [front, rest] at h
  simpa only [List.append_assoc, List.append_nil] using h

theorem frame_reserved_tail (r : Result) (digestLength : r.exportDigest.size = 32) :
    little (encodeResult r) 156 4 = 0 % 2^32 := by
  let front : List UInt8 := [76, 67, 51, 82] ++ word 2 (1) ++ word 2 (r.kind) ++ word 8 (r.run) ++
    word 8 (0) ++ word 4 (128) ++ word 4 (0) ++ word 4 (r.stage) ++ word 4 (r.detail) ++
    word 4 (entryWord r.entry) ++ word 4 ((if r.clean then 1 else 0)) ++ word 4 (r.triggers) ++
    word 4 (r.uid) ++ word 8 (r.cpu) ++ word 8 (r.peak) ++ word 8 (r.stdoutBytes) ++
    word 8 (r.stderrBytes) ++ word 8 (r.elapsed) ++ word 4 (r.exportState) ++ word 4 (r.omitted) ++
    r.exportDigest.data.toList ++ word 8 (r.oomKills) ++ word 8 (r.taskDenials) ++
    word 4 (r.exportError)
  let rest : List UInt8 := []
  have size : front.length = 156 := by
    simp only [front, List.length_append, word_length, List.length_cons, List.length_nil,
      Array.length_toList]
    cases r
    dsimp only [ByteArray.size] at digestLength ⊢
    omega
  have h := little_word front rest 4 (0)
  rw [size] at h
  delta encodeResult frameBytes
  dsimp only [front, rest] at h
  simpa only [List.append_assoc, List.append_nil] using h

theorem frame_magic (r : Result) : (encodeResult r).extract 0 4 = "LC3R".toUTF8 := by
  let rest : List UInt8 := word 2 (1) ++ word 2 (r.kind) ++ word 8 (r.run) ++ word 8 (0) ++
    word 4 (128) ++ word 4 (0) ++ word 4 (r.stage) ++ word 4 (r.detail) ++
    word 4 (entryWord r.entry) ++ word 4 ((if r.clean then 1 else 0)) ++ word 4 (r.triggers) ++
    word 4 (r.uid) ++ word 8 (r.cpu) ++ word 8 (r.peak) ++ word 8 (r.stdoutBytes) ++
    word 8 (r.stderrBytes) ++ word 8 (r.elapsed) ++ word 4 (r.exportState) ++ word 4 (r.omitted) ++
    r.exportDigest.data.toList ++ word 8 (r.oomKills) ++ word 8 (r.taskDenials) ++
    word 4 (r.exportError) ++ word 4 (0)
  have literal : ByteArray.mk #[76, 67, 51, 82] = "LC3R".toUTF8 := by decide
  rw [← literal]
  have h := extract_window [] [76, 67, 51, 82] rest
  delta encodeResult frameBytes
  dsimp only [rest] at h
  simpa only [List.length_nil, List.length_cons, List.nil_append, List.append_assoc,
    Nat.zero_add] using h

theorem frame_digest (r : Result) (digestLength : r.exportDigest.size = 32) :
    (encodeResult r).extract 104 136 = r.exportDigest := by
  let front : List UInt8 := [76, 67, 51, 82] ++ word 2 (1) ++ word 2 (r.kind) ++ word 8 (r.run) ++
    word 8 (0) ++ word 4 (128) ++ word 4 (0) ++ word 4 (r.stage) ++ word 4 (r.detail) ++
    word 4 (entryWord r.entry) ++ word 4 ((if r.clean then 1 else 0)) ++ word 4 (r.triggers) ++
    word 4 (r.uid) ++ word 8 (r.cpu) ++ word 8 (r.peak) ++ word 8 (r.stdoutBytes) ++
    word 8 (r.stderrBytes) ++ word 8 (r.elapsed) ++ word 4 (r.exportState) ++ word 4 (r.omitted)
  let rest : List UInt8 := word 8 (r.oomKills) ++ word 8 (r.taskDenials) ++ word 4 (r.exportError) ++
    word 4 (0)
  have size : front.length = 104 := by
    simp only [front, List.length_append, word_length, List.length_cons, List.length_nil]
  have len : r.exportDigest.data.toList.length = 32 := by
    simpa only [Array.length_toList, ByteArray.size] using digestLength
  have h := extract_window front r.exportDigest.data.toList rest
  rw [size, len] at h
  delta encodeResult frameBytes
  dsimp only [front, rest] at h
  simpa only [List.append_assoc, Array.toArray_toList] using h

theorem frame_header (r : Result) (digestLength : r.exportDigest.size = 32) :
    headerBad (encodeResult r) = false := by
  apply (headerBad_iff _).mpr
  refine ⟨?_, frame_magic r, ?_, ?_, ?_, ?_, ?_⟩
  · rw [frame_length, digestLength]
  · exact frame_version r
  · exact frame_sequence r
  · exact frame_payload_length r
  · exact frame_reserved_header r
  · exact frame_reserved_tail r digestLength

theorem frame_entry_exact (r : Result) : little (encodeResult r) 40 4 = entryWord r.entry := by
  have h := frame_entry r
  cases entry : r.entry <;> simpa only [entry, entryWord] using h

theorem frame_cleanup_exact (r : Result) :
    little (encodeResult r) 44 4 = (if r.clean then 1 else 0) := by
  have h := frame_cleanup r
  cases clean : r.clean <;> simpa only [clean, Bool.false_eq_true, ite_false, ite_true] using h

theorem frame_fields (r : Result) (widths : Widths r)
    (digestLength : r.exportDigest.size = 32) : fields (encodeResult r) r.entry = r := by
  obtain ⟨kind, stage, detail, triggers, uid, run, cpu, peak, stdout, stderr, elapsed,
    exportState, omitted, oom, tasks, exportError⟩ := widths
  unfold fields
  rw [frame_kind, frame_stage, frame_detail, frame_cleanup_exact, frame_triggers, frame_uid,
    frame_run, frame_cpu, frame_peak, frame_stdout, frame_stderr, frame_elapsed,
    frame_export_state, frame_omitted, frame_digest r digestLength, frame_oom r digestLength,
    frame_tasks r digestLength, frame_export_error r digestLength]
  rw [Nat.mod_eq_of_lt kind, Nat.mod_eq_of_lt stage, Nat.mod_eq_of_lt detail,
    Nat.mod_eq_of_lt triggers, Nat.mod_eq_of_lt uid, Nat.mod_eq_of_lt run,
    Nat.mod_eq_of_lt cpu, Nat.mod_eq_of_lt peak, Nat.mod_eq_of_lt stdout,
    Nat.mod_eq_of_lt stderr, Nat.mod_eq_of_lt elapsed, Nat.mod_eq_of_lt exportState,
    Nat.mod_eq_of_lt omitted, Nat.mod_eq_of_lt oom, Nat.mod_eq_of_lt tasks,
    Nat.mod_eq_of_lt exportError]
  cases r with
  | mk k s d e clean t u r c p out err elapsed estate omitted digest oom tasks error =>
    cases clean <;> rfl

theorem decode_encode (r : Result) (widths : Widths r)
    (digestLength : r.exportDigest.size = 32) :
    decodeResult (encodeResult r) = validateResult r := by
  rw [live_decode_view, parserView_complete (encodeResult r) r.entry
    (frame_header r digestLength) (frame_entry_exact r) (by
      rw [frame_cleanup_exact]
      cases r.clean <;> decide)]
  rw [frame_fields r widths digestLength]
  rfl

theorem decode_encode_iff (r : Result) (widths : Widths r)
    (digestLength : r.exportDigest.size = 32) :
    decodeResult (encodeResult r) = .ok r ↔ resultValid r = true := by
  rw [decode_encode r widths digestLength]
  unfold validateResult
  split <;> simp_all

end LeanCageM4.PublicEncode

-- §AR-m4-public.evidence: Ordinary kernel proofs of useful acceptance and explicit rejection.
namespace LeanCageM4.PublicWitnesses
open LeanCageM3 LeanCageM4.PublicWire LeanCageM4.PublicEncode

def sample (kind stage detail : Nat) (entry : Entry) (triggers : Nat := 0) : Result :=
  ⟨kind, stage, detail, entry, true, triggers, 100000, 1, 0, 0, 0, 0, 0,
    0, 0, ByteArray.mk (Array.replicate 32 0), 0, 0, 0⟩

def exited := sample 0 0 42 .yes
def setup := sample 1 8 13 .no
def signaled := sample 2 0 9 .yes
def cancelled := sample 3 0 0 .unknown 1
def unknown := sample 4 9 71 .unknown
def preflight : Result := { sample 7 0 0 .no with uid := 0, run := 0 }
def admitted := sample 5 0 0 .no
def entered := sample 6 8 0 .yes
def highKind := sample 256 0 42 .yes
def signal65 := sample 2 0 65 .yes

theorem exited_accepted :
    decodeResult (encodeResult exited) = .ok exited := by
  rw [decode_encode exited (by unfold Widths; decide) (by decide)]
  have valid : resultValid exited = true := by decide
  simp [validateResult, valid]

theorem setup_accepted :
    decodeResult (encodeResult setup) = .ok setup := by
  rw [decode_encode setup (by unfold Widths; decide) (by decide)]
  have valid : resultValid setup = true := by decide
  simp [validateResult, valid]

theorem signaled_accepted :
    decodeResult (encodeResult signaled) = .ok signaled := by
  rw [decode_encode signaled (by unfold Widths; decide) (by decide)]
  have valid : resultValid signaled = true := by decide
  simp [validateResult, valid]

theorem cancelled_accepted :
    decodeResult (encodeResult cancelled) = .ok cancelled := by
  rw [decode_encode cancelled (by unfold Widths; decide) (by decide)]
  have valid : resultValid cancelled = true := by decide
  simp [validateResult, valid]

theorem unknown_accepted :
    decodeResult (encodeResult unknown) = .ok unknown := by
  rw [decode_encode unknown (by unfold Widths; decide) (by decide)]
  have valid : resultValid unknown = true := by decide
  simp [validateResult, valid]

theorem preflight_accepted :
    decodeResult (encodeResult preflight) = .ok preflight := by
  rw [decode_encode preflight (by unfold Widths; decide) (by decide)]
  have valid : resultValid preflight = true := by decide
  simp [validateResult, valid]

theorem admitted_rejected :
    decodeResult (encodeResult admitted) = .error "inconsistent private result" := by
  rw [decode_encode admitted (by unfold Widths; decide) (by decide)]
  have valid : resultValid admitted = false := by decide
  simp [validateResult, valid]

theorem entered_rejected :
    decodeResult (encodeResult entered) = .error "inconsistent private result" := by
  rw [decode_encode entered (by unfold Widths; decide) (by decide)]
  have valid : resultValid entered = false := by decide
  simp [validateResult, valid]

theorem highKind_rejected :
    decodeResult (encodeResult highKind) = .error "inconsistent private result" := by
  rw [decode_encode highKind (by unfold Widths; decide) (by decide)]
  have valid : resultValid highKind = false := by decide
  simp [validateResult, valid]

theorem signal65_rejected :
    decodeResult (encodeResult signal65) = .error "inconsistent private result" := by
  rw [decode_encode signal65 (by unfold Widths; decide) (by decide)]
  have valid : resultValid signal65 = false := by decide
  simp [validateResult, valid]

end LeanCageM4.PublicWitnesses
