import LeanCageHost.GatewayWire

namespace LeanCage.Host.WireJson

def surrogateByte (byte : UInt8) : ByteArray :=
  ("\\udc" ++ String.ofList [Json.hexChar (byte.toNat / 16), Json.hexChar (byte.toNat % 16)]).toUTF8

-- §FS-host-boundary.caller: OS strings use scalar UTF-8 or the exact surrogateescape byte.
def pathBody : Nat → List UInt8 → ByteArray → ByteArray
  | 0, _, encoded => encoded
  | _, [], encoded => encoded
  | fuel + 1, byte :: rest, encoded =>
    if byte.toNat < 128 then
      pathBody fuel rest (encoded ++ (String.ofList (Json.escapeChar (Char.ofNat byte.toNat))).toUTF8)
    else
      let width := if 194 ≤ byte.toNat && byte.toNat ≤ 223 then 2
        else if 224 ≤ byte.toNat && byte.toNat ≤ 239 then 3
        else if 240 ≤ byte.toNat && byte.toNat ≤ 244 then 4 else 0
      let candidate := ByteArray.mk ((byte :: rest).take width).toArray
      if width != 0 && candidate.size == width && (String.fromUTF8? candidate).isSome then
        pathBody fuel (rest.drop (width - 1)) (encoded ++ candidate)
      else pathBody fuel rest (encoded ++ surrogateByte byte)

def path (bytes : ByteArray) : ByteArray :=
  "\"".toUTF8 ++ pathBody bytes.size bytes.data.toList .empty ++ "\"".toUTF8

-- §FS-host-boundary.publication: Human JSON is a projection of the same lossless typed envelope.
def render : Nat → GatewayWire.Value → Except String ByteArray
  | 0, _ => .error "public JSON depth exceeded"
  | depth + 1, value => do
    match value with
    | .null => return "null".toUTF8
    | .boolean true => return "true".toUTF8
    | .boolean false => return "false".toUTF8
    | .integer value => return (toString value).toUTF8
    | .string value => return Json.render (.string value)
    | .path bytes =>
      if bytes.size > GatewayWire.pathMax || bytes.data.contains 0 then
        throw "invalid public OS path"
      return path bytes
    | .number bytes =>
      match Json.parse bytes reportMax with
      | .ok (.number lexical) =>
        if ByteArray.mk lexical.toArray != bytes then throw "noncanonical public JSON number"
        return bytes
      | _ => throw "invalid public JSON number"
    | .bytes _ => throw "binary artifact cannot occur inside public metadata"
    | .array values =>
      let values ← values.mapM (render depth)
      return "[".toUTF8 ++
        (values.foldl (fun (state : Bool × ByteArray) bytes =>
          (false, state.2 ++ (if state.1 then .empty else ",".toUTF8) ++ bytes)) (true, .empty)).2 ++ "]".toUTF8
    | .object fields =>
      let fields ← fields.mapM (fun (key, value) => do
        return Json.render (.string key) ++ ":".toUTF8 ++ (← render depth value))
      return "{".toUTF8 ++
        (fields.foldl (fun (state : Bool × ByteArray) bytes =>
          (false, state.2 ++ (if state.1 then .empty else ",".toUTF8) ++ bytes)) (true, .empty)).2 ++ "}".toUTF8

end LeanCage.Host.WireJson
