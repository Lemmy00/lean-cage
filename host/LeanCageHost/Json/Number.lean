import LeanCageHost.Json.Types

namespace LeanCage.Host.Json

-- §FS-host-boundary.artifacts: The finite grammar retains exponent and sign spelling exactly.
inductive NumberState where
  | start | minus | zero | integer | dot | fraction | exponent | exponentSign | exponentDigits
  deriving DecidableEq, Repr

def numberTransition (state : NumberState) (c : Char) : Option NumberState :=
  match state with
  | .start =>
    if c = '-' then some .minus
    else if c = '0' then some .zero
    else if '1' ≤ c ∧ c ≤ '9' then some .integer else none
  | .minus =>
    if c = '0' then some .zero
    else if '1' ≤ c ∧ c ≤ '9' then some .integer else none
  | .zero =>
    if c = '.' then some .dot
    else if c = 'e' ∨ c = 'E' then some .exponent else none
  | .integer =>
    if '0' ≤ c ∧ c ≤ '9' then some .integer
    else if c = '.' then some .dot
    else if c = 'e' ∨ c = 'E' then some .exponent else none
  | .dot => if '0' ≤ c ∧ c ≤ '9' then some .fraction else none
  | .fraction =>
    if '0' ≤ c ∧ c ≤ '9' then some .fraction
    else if c = 'e' ∨ c = 'E' then some .exponent else none
  | .exponent =>
    if c = '+' ∨ c = '-' then some .exponentSign
    else if '0' ≤ c ∧ c ≤ '9' then some .exponentDigits else none
  | .exponentSign | .exponentDigits =>
    if '0' ≤ c ∧ c ≤ '9' then some .exponentDigits else none

def numberAccepting : NumberState → Bool
  | .zero | .integer | .fraction | .exponentDigits => true
  | _ => false

inductive NumberPrefix : List Char → NumberState → Prop where
  | start : NumberPrefix [] .start
  | step {chars : List Char} {state next : NumberState} {c : Char}
      (earlier : NumberPrefix chars state) (token : numberTransition state c = some next) :
      NumberPrefix (chars ++ [c]) next

def NumberToken (input : List Char) (bytes : List UInt8) (rest : List Char) : Prop :=
  ∃ chars state, input = chars ++ rest ∧ NumberPrefix chars state ∧
    numberAccepting state = true ∧ bytes = (String.ofList chars).toUTF8.data.toList

structure NumberResult (input : List Char) where
  bytes : List UInt8
  rest : List Char
  grammar : NumberToken input bytes rest

-- §AR-host-boundary.interfaces: A nonaccepting numeric prefix is an explicit error.
def readNumberLoop (original input acc : List Char) (state : NumberState)
    (split : original = acc.reverse ++ input) (earlier : NumberPrefix acc.reverse state) :
    Except String (NumberResult original) :=
  match input with
  | [] =>
    if accepting : numberAccepting state = true then
      .ok ⟨(String.ofList acc.reverse).toUTF8.data.toList, [],
        ⟨acc.reverse, state, split, earlier, accepting, rfl⟩⟩
    else .error "incomplete JSON number"
  | c :: rest =>
    match token : numberTransition state c with
    | some next => readNumberLoop original rest (c :: acc) next
        (by simpa [List.reverse_cons, List.append_assoc] using split)
        (by simpa [List.reverse_cons] using NumberPrefix.step earlier token)
    | none =>
      if accepting : numberAccepting state = true then
        .ok ⟨(String.ofList acc.reverse).toUTF8.data.toList, c :: rest,
          ⟨acc.reverse, state, split, earlier, accepting, rfl⟩⟩
      else .error "invalid JSON number"
termination_by input.length

def readNumber (input : List Char) : Except String (NumberResult input) :=
  readNumberLoop input input [] .start rfl .start

-- §FS-host-boundary.artifacts: Natural getters accept only canonical unsigned integer tokens.
def naturalDigits (acc : Nat) : List UInt8 → Option Nat
  | [] => some acc
  | byte :: rest =>
    if 48 ≤ byte.toNat ∧ byte.toNat ≤ 57 then
      naturalDigits (10 * acc + byte.toNat - 48) rest
    else none

def naturalToken? : List UInt8 → Option Nat
  | byte :: rest =>
    if byte = 48 then if rest = [] then some 0 else none
    else if 49 ≤ byte.toNat ∧ byte.toNat ≤ 57 then naturalDigits (byte.toNat - 48) rest
    else none
  | [] => none

def natural? : Value → Option Nat
  | .number bytes => naturalToken? bytes
  | _ => none

-- §FS-host-boundary.artifacts: Reject overflow before constructing a larger arbitrary integer.
def naturalDigitsBelow (acc maximum : Nat) : List UInt8 → Option Nat
  | [] => if acc ≤ maximum then some acc else none
  | byte :: rest =>
    if 48 ≤ byte.toNat ∧ byte.toNat ≤ 57 then
      let digit := byte.toNat - 48
      if digit ≤ maximum ∧ acc ≤ (maximum - digit) / 10 then
        naturalDigitsBelow (10 * acc + digit) maximum rest
      else none
    else none

def naturalTokenBelow? (bytes : List UInt8) (maximum : Nat) : Option Nat :=
  match bytes with
  | [] => none
  | byte :: rest =>
    if byte = 48 then if rest = [] then some 0 else none
    else if 49 ≤ byte.toNat ∧ byte.toNat ≤ 57 then
      naturalDigitsBelow (byte.toNat - 48) maximum rest
    else none

def naturalBelow? (value : Value) (maximum : Nat) : Option Nat :=
  match value with
  | .number bytes => naturalTokenBelow? bytes maximum
  | _ => none

-- §AR-host-boundary.interfaces: The semantic relation states the exact base-ten arithmetic.
inductive NaturalDigits : Nat → List UInt8 → Nat → Prop where
  | nil (value : Nat) : NaturalDigits value [] value
  | cons {acc value : Nat} {byte : UInt8} {rest : List UInt8}
      (digit : 48 ≤ byte.toNat ∧ byte.toNat ≤ 57)
      (tail : NaturalDigits (10 * acc + byte.toNat - 48) rest value) :
      NaturalDigits acc (byte :: rest) value

def NaturalToken (bytes : List UInt8) (value : Nat) : Prop :=
  (bytes = [48] ∧ value = 0) ∨ ∃ byte rest, bytes = byte :: rest ∧
    49 ≤ byte.toNat ∧ byte.toNat ≤ 57 ∧ NaturalDigits (byte.toNat - 48) rest value

theorem naturalDigits_exact (acc : Nat) (bytes : List UInt8) (value : Nat) :
    naturalDigits acc bytes = some value ↔ NaturalDigits acc bytes value := by
  induction bytes generalizing acc with
  | nil =>
    simp only [naturalDigits, Option.some.injEq]
    constructor
    · rintro rfl
      exact .nil _
    · intro h
      cases h
      rfl
  | cons byte rest ih =>
    simp only [naturalDigits]
    split
    · rw [ih]
      constructor
      · exact NaturalDigits.cons ‹_›
      · intro h
        cases h with | cons _ tail => exact tail
    · constructor
      · intro h
        cases h
      · intro h
        cases h with | cons digit _ => exact False.elim (‹¬ _› digit)

theorem naturalDigits_lower {acc value : Nat} {bytes : List UInt8}
    (meaning : NaturalDigits acc bytes value) : acc ≤ value := by
  induction meaning with
  | nil => exact Nat.le_refl _
  | cons digit _ ih => omega

theorem naturalDigitsBelow_exact (acc maximum : Nat) (bytes : List UInt8) (value : Nat) :
    naturalDigitsBelow acc maximum bytes = some value ↔
      NaturalDigits acc bytes value ∧ value ≤ maximum := by
  induction bytes generalizing acc with
  | nil =>
    simp only [naturalDigitsBelow]
    split
    · constructor
      · intro h
        cases h
        exact ⟨.nil _, ‹_›⟩
      · rintro ⟨meaning, _⟩
        cases meaning
        rfl
    · constructor
      · intro h
        cases h
      · rintro ⟨meaning, bounded⟩
        cases meaning
        contradiction
  | cons byte rest ih =>
    simp only [naturalDigitsBelow]
    split
    · rename_i digit
      have stepArithmetic : 10 * acc + (byte.toNat - 48) = 10 * acc + byte.toNat - 48 := by omega
      split
      · rename_i fits
        rw [ih, stepArithmetic]
        constructor
        · rintro ⟨tail, bound⟩
          exact ⟨.cons digit tail, bound⟩
        · rintro ⟨meaning, bound⟩
          cases meaning with | cons _ tail => exact ⟨tail, bound⟩
      · rename_i overflow
        constructor
        · intro h
          cases h
        · rintro ⟨meaning, bound⟩
          cases meaning with
          | cons _ tail =>
            have lower := naturalDigits_lower tail
            have fits : byte.toNat - 48 ≤ maximum ∧ acc ≤ (maximum - (byte.toNat - 48)) / 10 := by
              omega
            exact False.elim (overflow fits)
    · constructor
      · intro h
        cases h
      · rintro ⟨meaning, _⟩
        cases meaning with | cons digit _ => contradiction

end LeanCage.Host.Json
