import LeanCageHost.Json.Parser

namespace LeanCage.Host.Json

def hexChar (digit : Nat) : Char :=
  if digit < 10 then Char.ofNat (48 + digit) else Char.ofNat (87 + digit)

-- §FS-host-boundary.artifacts: Render strings with JSON escapes, preserving all Unicode scalars.
def escapeChar (c : Char) : List Char :=
  if c = '"' then ['\\', '"']
  else if c = '\\' then ['\\', '\\']
  else if c.toNat < 32 then ['\\', 'u', '0', '0', hexChar (c.toNat / 16), hexChar (c.toNat % 16)]
  else [c]

def quotedChars (text : String) : List Char :=
  '"' :: (text.toList.flatMap escapeChar ++ ['"'])

def encodedChars (chars : List Char) : List UInt8 :=
  (String.ofList chars).toUTF8.data.toList

-- §AR-host-boundary.interfaces: Rendering is total structural recursion, with no opaque parser.
def renderRaw (value : Value) : List UInt8 :=
  match value with
  | .null => [110, 117, 108, 108]
  | .bool true => [116, 114, 117, 101]
  | .bool false => [102, 97, 108, 115, 101]
  | .number bytes => bytes
  | .string text => encodedChars (quotedChars text)
  | .array values =>
    [91] ++ (List.intercalate [44] (values.toList.attach.map fun child => renderRaw child.val)) ++ [93]
  | .object fields =>
    [123] ++ (List.intercalate [44] (fields.attach.map fun field =>
      encodedChars (quotedChars field.val.1) ++ [58] ++ renderRaw field.val.2)) ++ [125]
termination_by value
decreasing_by
  · have member := Array.sizeOf_lt_of_mem (by simpa using child.property)
    simp_all
    omega
  · have member := List.sizeOf_lt_of_mem field.property
    have second : sizeOf field.val.2 < sizeOf field.val := by
      cases field.val
      simp
      omega
    simp_all
    omega

def render (value : Value) : ByteArray := ⟨(renderRaw value).toArray⟩

end LeanCage.Host.Json
