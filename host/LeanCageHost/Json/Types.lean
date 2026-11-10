import Std

namespace LeanCage.Host.Json

-- §FS-host-boundary.artifacts: JSON numbers retain their lexical bytes without rounding.
inductive Value where
  | null
  | bool (value : Bool)
  | number (bytes : List UInt8)
  | string (value : String)
  | array (values : Array Value)
  | object (fields : List (String × Value))
  deriving Inhabited, Repr, BEq

-- §FS-host-boundary.artifacts: Lookup uses the decoded key, including escaped aliases.
def get? : Value → String → Option Value
  | .object fields, key => (fields.find? (fun field => field.1 == key)).map Prod.snd
  | _, _ => none

-- §AR-host-boundary.interfaces: Containers consume depth; scalar values do not.
inductive WithinDepth : Nat → Value → Prop where
  | null (depth : Nat) : WithinDepth depth .null
  | bool (depth : Nat) (value : Bool) : WithinDepth depth (.bool value)
  | number (depth : Nat) (bytes : List UInt8) : WithinDepth depth (.number bytes)
  | string (depth : Nat) (value : String) : WithinDepth depth (.string value)
  | array {depth : Nat} {values : Array Value}
      (children : ∀ value ∈ values.toList, WithinDepth depth value) :
      WithinDepth (depth + 1) (.array values)
  | object {depth : Nat} {fields : List (String × Value)}
      (children : ∀ field ∈ fields, WithinDepth depth field.2) :
      WithinDepth (depth + 1) (.object fields)

end LeanCage.Host.Json
