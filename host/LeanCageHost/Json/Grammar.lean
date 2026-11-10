import LeanCageHost.Json.Number
import LeanCageHost.Json.Unicode

namespace LeanCage.Host.Json

-- §AR-host-boundary.interfaces: JSON whitespace is exactly SP, TAB, CR and LF.
inductive Spaces : List Char → List Char → Prop where
  | done (input : List Char) : Spaces input input
  | step {c : Char} {input rest : List Char} (space : c.isWhitespace = true)
      (tail : Spaces input rest) : Spaces (c :: input) rest

def skipSpaces : (input : List Char) → {rest : List Char // Spaces input rest}
  | [] => ⟨[], .done []⟩
  | c :: rest =>
    if space : c.isWhitespace = true then
      let result := skipSpaces rest
      ⟨result.val, .step space result.property⟩
    else ⟨c :: rest, .done _⟩

-- §FS-host-boundary.artifacts: The grammar fixes delimiters, decoded keys and every child value.
mutual
  inductive Syntax : List Char → Value → List Char → Prop where
    | spaces {input start rest : List Char} {value : Value}
        (space : Spaces input start) (valueSyntax : Syntax start value rest) :
        Syntax input value rest
    | null (rest : List Char) : Syntax ('n' :: 'u' :: 'l' :: 'l' :: rest) .null rest
    | true (rest : List Char) : Syntax ('t' :: 'r' :: 'u' :: 'e' :: rest) (.bool true) rest
    | false (rest : List Char) : Syntax ('f' :: 'a' :: 'l' :: 's' :: 'e' :: rest) (.bool false) rest
    | number {input rest : List Char} {bytes : List UInt8}
        (token : NumberToken input bytes rest) : Syntax input (.number bytes) rest
    | string {input decoded rest : List Char} (token : StringBody input decoded rest) :
        Syntax ('"' :: input) (.string (String.ofList decoded)) rest
    | emptyArray {input rest : List Char} (space : Spaces input (']' :: rest)) :
        Syntax ('[' :: input) (.array #[]) rest
    | array {input after rest : List Char} {values : Array Value}
        (members : ArrayMembers input values after) (space : Spaces after (']' :: rest)) :
        Syntax ('[' :: input) (.array values) rest
    | emptyObject {input rest : List Char} (space : Spaces input ('}' :: rest)) :
        Syntax ('{' :: input) (.object []) rest
    | object {input after rest : List Char} {fields : List (String × Value)}
        (members : ObjectMembers input fields after) (space : Spaces after ('}' :: rest)) :
        Syntax ('{' :: input) (.object fields) rest

  inductive ArrayMembers : List Char → Array Value → List Char → Prop where
    | first {input rest : List Char} {value : Value} (valueSyntax : Syntax input value rest) :
        ArrayMembers input #[value] rest
    | next {input after more rest : List Char} {values : Array Value} {value : Value}
        (earlier : ArrayMembers input values after) (space : Spaces after (',' :: more))
        (valueSyntax : Syntax more value rest) : ArrayMembers input (values.push value) rest

  inductive ObjectMembers : List Char → List (String × Value) → List Char → Prop where
    | first {input afterKey more rest : List Char} {key : String} {value : Value}
        (keySyntax : Syntax input (.string key) afterKey) (colon : Spaces afterKey (':' :: more))
        (valueSyntax : Syntax more value rest) : ObjectMembers input [(key, value)] rest
    | next {input after nextKey afterKey more rest : List Char}
        {fields : List (String × Value)} {key : String} {value : Value}
        (earlier : ObjectMembers input fields after) (comma : Spaces after (',' :: nextKey))
        (keySyntax : Syntax nextKey (.string key) afterKey) (colon : Spaces afterKey (':' :: more))
        (valueSyntax : Syntax more value rest) (fresh : key ∉ fields.map Prod.fst) :
        ObjectMembers input (fields ++ [(key, value)]) rest
end

structure Parsed (depth : Nat) (input : List Char) where
  value : Value
  rest : List Char
  grammar : Syntax input value rest
  bounded : WithinDepth depth value

structure KeyResult (input : List Char) where
  key : String
  rest : List Char
  grammar : Syntax input (.string key) rest

def readKey (input : List Char) : Except String (KeyResult input) := do
  let start := skipSpaces input
  match shape : start.val with
  | '"' :: rest =>
    let key ← readString rest
    return ⟨String.ofList key.decoded, key.rest,
      .spaces (shape ▸ start.property) (.string key.grammar)⟩
  | _ => .error "expected JSON object key"

structure MemberResult (depth : Nat) (input : List Char) where
  key : String
  value : Value
  rest : List Char
  afterKey : List Char
  more : List Char
  keyGrammar : Syntax input (.string key) afterKey
  colon : Spaces afterKey (':' :: more)
  valueGrammar : Syntax more value rest
  bounded : WithinDepth depth value

end LeanCage.Host.Json
