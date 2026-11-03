namespace LeanCage.Entry.Arguments

-- §FS-entry.inputs: The private worker ABI uses canonical ASCII decimals with explicit bounds.
def digit (limit value : Nat) (byte : UInt8) : Option Nat :=
  if byte.toNat < 48 || byte.toNat > 57 then none
  else
    let next := value * 10 + (byte.toNat - 48)
    if next ≤ limit then some next else none

def digits (limit value : Nat) : List UInt8 → Option Nat
  | [] => some value
  | byte :: rest => (digit limit value byte).bind (fun next => digits limit next rest)

def unsigned (limit : Nat) (bytes : List UInt8) : Option Nat :=
  match bytes with
  | [] => none
  | first :: rest =>
    if first.toNat == 48 && !rest.isEmpty then none else digits limit 0 bytes

theorem digit_bound {limit initial value : Nat} {byte : UInt8}
    (parsed : digit limit initial byte = some value) : value ≤ limit := by
  unfold digit at parsed
  split at parsed
  · contradiction
  · dsimp only at parsed
    split at parsed
    · cases parsed
      assumption
    · contradiction

theorem digits_bound {limit initial value : Nat} {bytes : List UInt8}
    (start : initial ≤ limit) (parsed : digits limit initial bytes = some value) : value ≤ limit := by
  induction bytes generalizing initial with
  | nil => cases parsed; exact start
  | cons byte rest ih =>
    simp only [digits] at parsed
    cases step : digit limit initial byte with
    | none => simp [step] at parsed
    | some next => exact ih (digit_bound step) (by simpa [step] using parsed)

theorem unsigned_bound {limit value : Nat} {bytes : List UInt8}
    (parsed : unsigned limit bytes = some value) : value ≤ limit := by
  cases bytes with
  | nil => contradiction
  | cons first rest =>
    change (if first.toNat == 48 && !rest.isEmpty then none else
      digits limit 0 (first :: rest)) = some value at parsed
    split at parsed
    · contradiction
    · exact digits_bound (Nat.zero_le _) parsed

theorem unsigned_empty (limit : Nat) : unsigned limit [] = none := rfl

theorem useful_uid : unsigned 100999 [49, 48, 48, 48, 48, 48] = some 100000 := by decide
theorem leading_zero_rejected : unsigned 2147483647 [48, 52] = none := by decide
theorem overflow_rejected : unsigned 2147483647 [50, 49, 52, 55, 52, 56, 51, 54, 52, 56] = none := by decide

end LeanCage.Entry.Arguments
