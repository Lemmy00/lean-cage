import JsonProofs

open LeanCage.Host.Json

-- §FS-host-boundary.artifacts: Exercise exact values and hostile encodings through the live parser.
private def check (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw <| IO.userError ("JSON check failed: " ++ label)

private def accepted (bytes : ByteArray) (value : Value) : Bool :=
  match parse bytes bytes.size with
  | .ok actual => actual == value
  | .error _ => false

private def rejected (bytes : ByteArray) : Bool :=
  match parse bytes bytes.size with
  | .ok _ => false
  | .error _ => true

private def number (text : String) : Value := .number text.toUTF8.data.toList

private def nested : Nat → Value
  | 0 => .null
  | depth + 1 => .array #[nested depth]

def main (args : List String) : IO Unit := do
  check "mixed report values" (accepted
    " {\"ok\":true,\"nil\":null,\"array\":[false,0,-1.25e+2],\"s\":\"\\uD83D\\uDE00\"} \r\n".toUTF8
    (.object [("ok", .bool true), ("nil", .null),
      ("array", .array #[.bool false, number "0", number "-1.25e+2"]), ("s", .string "😀")]))
  for invalid in ["", "true false", "[1,]", "[,1]", "{\"a\":0,}", "{a:0}",
      "01", "-01", "+1", "1.", "1e", "1e+", "NaN", "Infinity", "\"\\q\"",
      "\"\\uD800\"", "\"\\uDC00\"", "\"\\uD800\\u0041\"", "\"\n\""] do
    check ("malformed " ++ reprStr invalid) (rejected invalid.toUTF8)
  check "escaped ASCII duplicate" (rejected "{\"a\":0,\"\\u0061\":1}".toUTF8)
  check "escaped supplementary duplicate" (rejected "{\"😀\":0,\"\\uD83D\\uDE00\":1}".toUTF8)
  for bytes in [#[0xc0, 0x80], #[0xe2, 0x82], #[0xed, 0xa0, 0x80], #[0xf4, 0x90, 0x80, 0x80], #[0x80]] do
    check "strict UTF8" (rejected ⟨bytes⟩)
  let controls := String.ofList ((List.range 32).map Char.ofNat) ++ "😀\\\"/é"
  check "all controls and Unicode serialize" (accepted (render (.string controls)) (.string controls))
  let wide := Value.object ((List.range 80).map (fun index => ("field" ++ toString index, number "1")))
  check "report exceeds old 32-field cap" (accepted (render wide) wide)
  check "depth64 accepts" (accepted (render (nested 64)) (nested 64))
  check "depth65 rejects" (rejected (render (nested 65)))
  check "caller depth rejects" (match parseWithDepth "[[0]]".toUTF8 5 1 with
    | .error _ => true | _ => false)
  check "byte limit rejects first" (match parse "true".toUTF8 3 with
    | .error "JSON byte limit exceeded" => true | _ => false)
  let maximum := 18446744073709551615
  check "maximum uint64" (naturalBelow? (number "18446744073709551615") maximum == some maximum)
  for invalid in ["18446744073709551616", "-0", "01", "1e0", "1.0"] do
    check "bounded canonical integer" (naturalBelow? (number invalid) maximum == none)
  check "long number rejects before huge Nat" (naturalBelow? (.number (List.replicate 65536 57)) maximum == none)
  check "zero bound" (naturalBelow? (number "0") 0 == some 0)
  check "zero bound rejects one" (naturalBelow? (number "1") 0 == none)
  check "decoded getter" (get? (.object [("😀", .null)]) "😀" == some .null)
  for filename in args do
    let bytes ← IO.FS.readBinFile filename
    match parse bytes 65536 with
    | .error error => throw <| IO.userError (filename ++ ": " ++ error)
    | .ok value =>
      check ("actual report roundtrip " ++ filename) (accepted (render value) value)
  IO.println "JSON checks passed: bounded grammar, Unicode, decoded keys, reports, numeric limits and serialization."
