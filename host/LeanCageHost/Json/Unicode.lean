import Std

namespace LeanCage.Host.Json

-- §FS-host-boundary.artifacts: Hexadecimal escapes denote their exact scalar values.
def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def hexFour (a b c d : Char) : Option Nat := do
  let a ← hexDigit a
  let b ← hexDigit b
  let c ← hexDigit c
  let d ← hexDigit d
  return 4096 * a + 256 * b + 16 * c + d

def simpleEscape : Char → Option Char
  | '"' => some '"'
  | '\\' => some '\\'
  | '/' => some '/'
  | 'b' => some '\x08'
  | 'f' => some '\x0c'
  | 'n' => some '\n'
  | 'r' => some '\r'
  | 't' => some '\t'
  | _ => none

-- §AR-host-boundary.interfaces: This grammar interprets escapes, rather than retaining spelling.
inductive StringBody : List Char → List Char → List Char → Prop where
  | close (rest : List Char) : StringBody ('"' :: rest) [] rest
  | raw {c : Char} {input decoded rest : List Char}
      (allowed : 32 ≤ c.toNat ∧ c ≠ '"' ∧ c ≠ '\\')
      (tail : StringBody input decoded rest) : StringBody (c :: input) (c :: decoded) rest
  | escaped {escape c : Char} {input decoded rest : List Char}
      (meaning : simpleEscape escape = some c) (tail : StringBody input decoded rest) :
      StringBody ('\\' :: escape :: input) (c :: decoded) rest
  | scalar {a b c d : Char} {n : Nat} {input decoded rest : List Char}
      (digits : hexFour a b c d = some n) (valid : n.isValidChar)
      (tail : StringBody input decoded rest) :
      StringBody ('\\' :: 'u' :: a :: b :: c :: d :: input)
        (Char.ofNatAux n valid :: decoded) rest
  | pair {a b c d e f g h : Char} {hi lo : Nat} {input decoded rest : List Char}
      (highDigits : hexFour a b c d = some hi) (lowDigits : hexFour e f g h = some lo)
      (high : 0xd800 ≤ hi ∧ hi ≤ 0xdbff) (low : 0xdc00 ≤ lo ∧ lo ≤ 0xdfff)
      (valid : (65536 + 1024 * (hi - 0xd800) + (lo - 0xdc00)).isValidChar)
      (tail : StringBody input decoded rest) :
      StringBody ('\\' :: 'u' :: a :: b :: c :: d :: '\\' :: 'u' :: e :: f :: g :: h :: input)
        (Char.ofNatAux (65536 + 1024 * (hi - 0xd800) + (lo - 0xdc00)) valid :: decoded) rest

structure StringResult (input : List Char) where
  decoded : List Char
  rest : List Char
  grammar : StringBody input decoded rest

private theorem pushStringPrefix {original input next acc : List Char} {c : Char}
    (continuation : ∀ decoded rest, StringBody input decoded rest →
      StringBody original (acc.reverse ++ decoded) rest)
    (step : ∀ decoded rest, StringBody next decoded rest →
      StringBody input (c :: decoded) rest) :
    ∀ decoded rest, StringBody next decoded rest →
      StringBody original ((c :: acc).reverse ++ decoded) rest := by
  intro decoded rest grammar
  simpa [List.reverse_cons, List.append_assoc] using continuation (c :: decoded) rest (step _ _ grammar)

-- §FS-host-boundary.artifacts: The accumulator loop is total and preserves decoded scalar meaning.
def readStringLoop (original : List Char) (input acc : List Char)
    (continuation : ∀ decoded rest, StringBody input decoded rest →
      StringBody original (acc.reverse ++ decoded) rest) : Except String (StringResult original) :=
  match input with
  | [] => .error "unterminated JSON string"
  | '"' :: rest => .ok ⟨acc.reverse, rest, by simpa using continuation [] rest (.close rest)⟩
  | '\\' :: 'u' :: a :: b :: c :: d :: rest =>
    match digits : hexFour a b c d with
    | none => .error "invalid JSON Unicode escape"
    | some n =>
      if high : 0xd800 ≤ n ∧ n ≤ 0xdbff then
        match rest with
        | '\\' :: 'u' :: e :: f :: g :: h :: tail =>
          match lowDigits : hexFour e f g h with
          | none => .error "invalid JSON low surrogate"
          | some lo =>
            if low : 0xdc00 ≤ lo ∧ lo ≤ 0xdfff then
              have valid : (65536 + 1024 * (n - 0xd800) + (lo - 0xdc00)).isValidChar := by
                simp only [Nat.isValidChar]
                right
                omega
              readStringLoop original tail
                (Char.ofNatAux (65536 + 1024 * (n - 0xd800) + (lo - 0xdc00)) valid :: acc)
                (pushStringPrefix continuation (fun _ _ grammar => .pair digits lowDigits high low valid grammar))
            else .error "invalid JSON low surrogate"
        | _ => .error "missing JSON low surrogate"
      else if valid : n.isValidChar then
        readStringLoop original rest (Char.ofNatAux n valid :: acc)
          (pushStringPrefix continuation (fun _ _ grammar => .scalar digits valid grammar))
      else .error "unpaired JSON surrogate"
  | '\\' :: escape :: rest =>
    match meaning : simpleEscape escape with
    | none => .error "invalid JSON escape"
    | some c => readStringLoop original rest (c :: acc)
        (pushStringPrefix continuation (fun _ _ grammar => .escaped meaning grammar))
  | c :: rest =>
    if allowed : 32 ≤ c.toNat ∧ c ≠ '"' ∧ c ≠ '\\' then
      readStringLoop original rest (c :: acc)
        (pushStringPrefix continuation (fun _ _ grammar => .raw allowed grammar))
    else .error "unescaped JSON control character"
termination_by input.length

def readString (input : List Char) : Except String (StringResult input) :=
  readStringLoop input input [] (by intro decoded rest grammar; exact grammar)

-- §FS-host-boundary.artifacts: A successful strict decode identifies every original input byte.
theorem strict_utf8 {bytes : ByteArray} {text : String}
    (decoded : String.fromUTF8? bytes = some text) :
    bytes.IsValidUTF8 ∧ text.toUTF8 = bytes := by
  unfold String.fromUTF8? at decoded
  split at decoded
  · cases decoded
    exact ⟨‹bytes.IsValidUTF8›, rfl⟩
  · contradiction

end LeanCage.Host.Json
