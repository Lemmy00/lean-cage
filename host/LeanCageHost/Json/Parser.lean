import LeanCageHost.Json.Grammar

namespace LeanCage.Host.Json

-- §FS-host-boundary.artifacts: Every successful branch constructs its grammar certificate.
mutual
  def readValue : (fuel depth : Nat) → (input : List Char) → Except String (Parsed depth input)
    | 0, _, _ => .error "JSON parser fuel exhausted"
    | fuel + 1, depth, input => do
      let start := skipSpaces input
      let result : Except String (Parsed depth start.val) :=
        match shape : start.val with
        | 'n' :: 'u' :: 'l' :: 'l' :: rest => .ok ⟨.null, rest, .null rest, .null depth⟩
        | 't' :: 'r' :: 'u' :: 'e' :: rest => .ok ⟨.bool true, rest, .true rest, .bool depth true⟩
        | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: rest => .ok ⟨.bool false, rest, .false rest, .bool depth false⟩
        | '"' :: rest => do
          let string ← readString rest
          return ⟨.string (String.ofList string.decoded), string.rest, .string string.grammar,
            .string depth _⟩
        | '[' :: rest =>
          match depth with
          | 0 => .error "JSON nesting limit exceeded"
          | depth + 1 => do
            let first := skipSpaces rest
            match empty : first.val with
            | ']' :: after =>
              return ⟨.array #[], after, .emptyArray (empty ▸ first.property), .array (by simp)⟩
            | _ =>
              let value ← readValue fuel depth rest
              readArrayTail fuel depth rest #[value.value] value.rest (.first value.grammar)
                (by simpa using value.bounded)
        | '{' :: rest =>
          match depth with
          | 0 => .error "JSON nesting limit exceeded"
          | depth + 1 => do
            let first := skipSpaces rest
            match empty : first.val with
            | '}' :: after =>
              return ⟨.object [], after, .emptyObject (empty ▸ first.property), .object (by simp)⟩
            | _ =>
              let member ← readMember fuel depth rest
              readObjectTail fuel depth rest [(member.key, member.value)] member.rest
                (by simpa using ObjectMembers.first member.keyGrammar member.colon member.valueGrammar)
                (by simpa using member.bounded)
        | remaining => do
          let number ← readNumber remaining
          return ⟨.number number.bytes, number.rest, .number number.grammar, .number depth _⟩
      let value ← result
      return ⟨value.value, value.rest, .spaces start.property value.grammar, value.bounded⟩

  def readArrayTail : (fuel depth : Nat) → (original : List Char) → (values : Array Value) →
      (input : List Char) → ArrayMembers original values input →
      (∀ value ∈ values.toList, WithinDepth depth value) →
      Except String (Parsed (depth + 1) ('[' :: original))
    | 0, _, _, _, _, _, _ => .error "JSON parser fuel exhausted"
    | fuel + 1, depth, original, values, input, members, bounded => do
      let start := skipSpaces input
      match shape : start.val with
      | ']' :: rest =>
        return ⟨.array values, rest, .array members (shape ▸ start.property), .array bounded⟩
      | ',' :: rest =>
        let value ← readValue fuel depth rest
        readArrayTail fuel depth original (values.push value.value) value.rest
          (.next members (shape ▸ start.property) value.grammar)
          (by
            intro item present
            simp only [Array.toList_push, List.mem_append, List.mem_singleton] at present
            rcases present with old | rfl
            · exact bounded _ old
            · exact value.bounded)
      | _ => .error "expected JSON array separator"

  def readObjectTail : (fuel depth : Nat) → (original : List Char) →
      (reversed : List (String × Value)) → (input : List Char) →
      ObjectMembers original reversed.reverse input →
      (∀ field ∈ reversed, WithinDepth depth field.2) →
      Except String (Parsed (depth + 1) ('{' :: original))
    | 0, _, _, _, _, _, _ => .error "JSON parser fuel exhausted"
    | fuel + 1, depth, original, reversed, input, members, bounded => do
      let start := skipSpaces input
      match shape : start.val with
      | '}' :: rest =>
        return ⟨.object reversed.reverse, rest, .object members (shape ▸ start.property),
          .object (by simpa using bounded)⟩
      | ',' :: rest =>
        let member ← readMember fuel depth rest
        if duplicate : member.key ∈ reversed.map Prod.fst then
          .error "duplicate decoded JSON object key"
        else
          readObjectTail fuel depth original ((member.key, member.value) :: reversed) member.rest
            (by
              simpa using ObjectMembers.next members (shape ▸ start.property)
                member.keyGrammar member.colon member.valueGrammar (by simpa using duplicate))
            (by
              intro item present
              simp only [List.mem_cons] at present
              rcases present with rfl | old
              · exact member.bounded
              · exact bounded _ old)
      | _ => .error "expected JSON object separator"

  def readMember : (fuel depth : Nat) → (input : List Char) → Except String (MemberResult depth input)
    | 0, _, _ => .error "JSON parser fuel exhausted"
    | fuel + 1, depth, input => do
      let key ← readKey input
      let afterKey := skipSpaces key.rest
      match shape : afterKey.val with
      | ':' :: more =>
        let value ← readValue fuel depth more
        return ⟨key.key, value.value, value.rest, key.rest, more, key.grammar,
          shape ▸ afterKey.property, value.grammar, value.bounded⟩
      | _ => .error "expected JSON object colon"
end

-- §AR-host-boundary.interfaces: Bound bytes before decoding; objects have no policy field cap.
def parseCertified (bytes : ByteArray) (limit depthLimit : Nat) :
    Except String {value : Value // ∃ (text : String) (rest : List Char),
      String.fromUTF8? bytes = some text ∧ Syntax text.toList value rest ∧ Spaces rest [] ∧
      WithinDepth depthLimit value ∧ bytes.size ≤ limit} := do
  if bounded : bytes.size ≤ limit then
    match decoded : String.fromUTF8? bytes with
    | none => .error "invalid JSON UTF-8"
    | some text =>
      let input := text.toList
      let value ← readValue (4 * input.length + 4) depthLimit input
      let suffix := skipSpaces value.rest
      if finished : suffix.val = [] then
        return ⟨value.value, text, value.rest, decoded, value.grammar,
          finished ▸ suffix.property, value.bounded, bounded⟩
      else .error "trailing JSON bytes"
  else .error "JSON byte limit exceeded"

def parseWithDepth (bytes : ByteArray) (limit depthLimit : Nat) : Except String Value :=
  (parseCertified bytes limit depthLimit).map Subtype.val

def parse (bytes : ByteArray) (limit : Nat) : Except String Value :=
  parseWithDepth bytes limit 64

end LeanCage.Host.Json
