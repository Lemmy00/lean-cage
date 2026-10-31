import Public

-- §AR-m4-bridge.normalization: Preserve the complete live result, including exact errors.
namespace LeanCageM4.Normalized
open LeanCageM3 LeanCageM4.PublicWire

inductive ErrorCode where
  | header | entry | cleanup | validity
  deriving DecidableEq

def lookup : List UInt8 → Nat → UInt8
  | [], _ => 0
  | b :: _, 0 => b
  | _ :: bs, n + 1 => lookup bs n

def byteAt (bytes : ByteArray) (i : Nat) : UInt8 := lookup bytes.data.toList i

def littleBytes (bytes : ByteArray) (offset width : Nat) : Nat :=
  (List.range width).foldl (fun n i => n + (byteAt bytes (offset+i)).toNat * 2^(8*i)) 0

theorem lookup_exact (bytes : List UInt8) (i : Nat) :
    lookup bytes i = bytes[i]?.getD 0 := by
  induction bytes generalizing i with
  | nil => simp [lookup]
  | cons b bs ih => cases i <;> simp [lookup, ih]

theorem byteAt_exact (bytes : ByteArray) (i : Nat) :
    byteAt bytes i = bytes[i]?.getD 0 := by
  unfold byteAt
  rw [lookup_exact]
  simp only [getElem?_def, Array.length_toList, ByteArray.size]
  split <;> simp_all [ByteArray.getElem_eq_getElem_data]

theorem little_exact (bytes : ByteArray) (offset width : Nat) :
    littleBytes bytes offset width = little bytes offset width := by
  simp only [littleBytes, little, byteAt_exact]

def fieldsBytes (bytes : ByteArray) (entry : Entry) : Result :=
  ⟨littleBytes bytes 6 2, littleBytes bytes 32 4, littleBytes bytes 36 4, entry,
    littleBytes bytes 44 4 == 1, littleBytes bytes 48 4, littleBytes bytes 52 4, littleBytes bytes 8 8,
    littleBytes bytes 56 8, littleBytes bytes 64 8, littleBytes bytes 72 8, littleBytes bytes 80 8, littleBytes bytes 88 8,
    littleBytes bytes 96 4, littleBytes bytes 100 4, bytes.extract 104 136,
    littleBytes bytes 136 8, littleBytes bytes 144 8, littleBytes bytes 152 4⟩

theorem fields_exact (bytes : ByteArray) (entry : Entry) :
    fieldsBytes bytes entry = fields bytes entry := by
  simp only [fieldsBytes, fields, little_exact]

def headerBadBytes (bytes : ByteArray) : Bool :=
  bytes.size != 160 || bytes.extract 0 4 != ByteArray.mk #[76, 67, 51, 82] ||
  littleBytes bytes 4 2 != 1 || littleBytes bytes 16 8 != 0 || littleBytes bytes 24 4 != 128 ||
  littleBytes bytes 28 4 != 0 || littleBytes bytes 156 4 != 0

def validate (r : Result) : Except ErrorCode Result :=
  if resultValid r then .ok r else .error .validity

def parse (bytes : ByteArray) : Except ErrorCode Result := do
  if headerBadBytes bytes then throw ErrorCode.header
  let entry ← match littleBytes bytes 40 4 with
    | 0 => pure Entry.no
    | 1 => pure Entry.yes
    | 2 => pure Entry.unknown
    | _ => throw ErrorCode.entry
  if littleBytes bytes 44 4 > 1 then throw ErrorCode.cleanup
  return fieldsBytes bytes entry

def decode (bytes : ByteArray) : Except ErrorCode Result := do
  validate (← parse bytes)

def errorText : ErrorCode → String
  | .header => "invalid private result frame"
  | .entry => "invalid entry knowledge"
  | .cleanup => "invalid cleanup knowledge"
  | .validity => "inconsistent private result"

def restore : Except ErrorCode Result → Except String Result
  | .ok r => .ok r
  | .error e => .error (errorText e)

theorem header_exact (bytes : ByteArray) : headerBadBytes bytes = headerBad bytes := by
  have literal : ByteArray.mk #[76, 67, 51, 82] = "LC3R".toUTF8 := by decide
  simp only [headerBadBytes, headerBad, literal, little_exact]

theorem validate_exact (r : Result) : restore (validate r) = validateResult r := by
  unfold validate validateResult
  split <;> rfl

theorem parse_exact (bytes : ByteArray) : restore (parse bytes) = parserView bytes := by
  unfold parserView
  unfold_m3_parser
  unfold parse
  simp only [header_exact, little_exact, fields_exact]
  cases head : headerBad bytes with
  | true =>
    unfold headerBad at head
    simp only [head, ite_true]
    rfl
  | false =>
    unfold headerBad at head
    simp only [head, Bool.false_eq_true, ite_false]
    generalize code : little bytes 40 4 = n
    cases n with
    | zero =>
      by_cases clean : little bytes 44 4 > 1 <;> simp only [clean, ite_true, ite_false] <;> rfl
    | succ n =>
      cases n with
      | zero =>
        by_cases clean : little bytes 44 4 > 1 <;> simp only [clean, ite_true, ite_false] <;> rfl
      | succ n =>
        cases n with
        | zero =>
          by_cases clean : little bytes 44 4 > 1 <;> simp only [clean, ite_true, ite_false] <;> rfl
        | succ n => rfl

theorem decode_exact (bytes : ByteArray) : restore (decode bytes) = decodeResult bytes := by
  rw [live_decode_view, ← parse_exact]
  unfold decode
  cases parse bytes with
  | error e => rfl
  | ok r => exact validate_exact r

end LeanCageM4.Normalized
