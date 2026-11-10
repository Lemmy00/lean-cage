import LeanCageHost.Bytes
import LeanCageHost.Json

namespace LeanCage.Host.GatewayWire

-- §AR-host-boundary.interfaces: Request bytes carry values, never an executable selector.
def requestMagic : ByteArray := "LCHREQ1\x00".toUTF8
def responseMagic : ByteArray := "LCHRES1\x00".toUTF8
def requestHeader : Nat := 112
def responseHeader : Nat := 24
def pathMax : Nat := 4095
def requestMax : Nat := requestHeader + 8 * pathMax + reportMax + stdinMax + 8
def responseMax : Nat := 512 * 1024 * 1024
def valueDepthMax : Nat := 72
def valueNodeMax : Nat := 16 * inodeMax

def validateCommand : Nat := 0
def checkCommand : Nat := 1
def runCommand : Nat := 2
def reportCommand : Nat := 3
def bundleCommand : Nat := 4
def cliCommand : Nat := 5

def bundleSlot : Nat := 0
def resultsSlot : Nat := 1
def policySlot : Nat := 2
def workspaceSlot : Nat := 3
def stdinSlot : Nat := 4
def outputSlot : Nat := 5
def timeoutSlot : Nat := 6
def lookupSlot : Nat := 7

def absentKind : Nat := 0
def rawKind : Nat := 1
def pathKind : Nat := 2
def timeoutKind : Nat := 3

structure Field where
  kind : Nat := absentKind
  bytes : ByteArray := .empty
  deriving DecidableEq

structure Request where
  command : Nat
  fault : Nat := 0
  fields : Array Field
  deriving DecidableEq

def Request.field (request : Request) (index : Nat) : Field :=
  request.fields[index]?.getD {}

-- §FS-host-boundary.caller: OS names retain their filesystem bytes and reject embedded NUL.
def pathValid (field : Field) : Bool :=
  field.kind == pathKind && field.bytes.size ≤ pathMax &&
    !field.bytes.data.toList.contains 0

def fieldMax (index : Nat) : Nat :=
  if index == policySlot then reportMax
  else if index == stdinSlot then stdinMax
  else if index == timeoutSlot then 8
  else pathMax

def fieldValid (index : Nat) (field : Field) : Bool :=
  if field.kind == absentKind then field.bytes.isEmpty
  else if field.kind == pathKind then index != timeoutSlot && pathValid field
  else if field.kind == rawKind then
    (index == policySlot || index == stdinSlot) && field.bytes.size ≤ fieldMax index
  else field.kind == timeoutKind && index == timeoutSlot && field.bytes.size == 8

def Request.valid (request : Request) : Bool :=
  request.command ≤ cliCommand && request.fault ≤ 2 && request.fields.size == 8 &&
  (List.range 8).all (fun index => fieldValid index (request.field index)) &&
  pathValid (request.field bundleSlot) &&
  (request.fault == 0 || request.command == runCommand) &&
  (let empty := fun index => (request.field index).kind == absentKind
   if request.command == cliCommand then
     (request.field policySlot).kind == rawKind &&
       (empty resultsSlot || pathValid (request.field resultsSlot)) &&
       [workspaceSlot, stdinSlot, outputSlot, timeoutSlot, lookupSlot].all empty
   else if request.command == validateCommand then
     !empty policySlot && [workspaceSlot, stdinSlot, outputSlot, timeoutSlot, lookupSlot].all empty
   else if request.command == checkCommand || request.command == runCommand then
     !empty policySlot && empty lookupSlot
   else if request.command == reportCommand then
     pathValid (request.field lookupSlot) &&
       [policySlot, workspaceSlot, stdinSlot, outputSlot, timeoutSlot].all empty
   else [policySlot, workspaceSlot, stdinSlot, outputSlot, timeoutSlot, lookupSlot].all empty)

def encodeRequest (request : Request) : ByteArray :=
  let fields := (List.range 8).map request.field
  let header := requestMagic ++ littleEndian 4 request.command ++ littleEndian 4 request.fault
  let header := fields.foldl (fun bytes field =>
    bytes ++ littleEndian 4 field.kind ++ littleEndian 8 field.bytes.size) header
  fields.foldl (fun bytes field => bytes ++ field.bytes) header

private def readWord (bytes : ByteArray) (offset width : Nat) : Nat :=
  fromLittleEndian (bytes.extract offset (offset + width))

-- §FS-host-boundary.caller: Structural descent consumes one checked field at a time.
def decodeFields (bytes : ByteArray) :
    List Nat → Nat → Array Field → Except String (Nat × Array Field)
  | [], position, fields => .ok (position, fields)
  | index :: rest, position, fields => do
    let kind := readWord bytes (16 + 12 * index) 4
    let size := readWord bytes (20 + 12 * index) 8
    if size > fieldMax index || size > bytes.size - position then
      throw "host request field exceeds its bound"
    decodeFields bytes rest (position + size)
      (fields.push ⟨kind, bytes.extract position (position + size)⟩)

-- §FS-host-boundary.caller: Check all lengths before selecting the corresponding byte slice.
def decodeRequest (bytes : ByteArray) : Except String Request := do
  if bytes.size < requestHeader || bytes.size > requestMax ||
      bytes.extract 0 8 != requestMagic then throw "invalid host request header"
  let command := readWord bytes 8 4
  let fault := readWord bytes 12 4
  let (position, fields) ← decodeFields bytes (List.range 8) requestHeader #[]
  let request := Request.mk command fault fields
  if position != bytes.size || !request.valid then throw "inconsistent host request"
  return request

-- §FS-host-boundary.caller: Typed return values have explicit constructors at the Python boundary.
inductive Value where
  | null
  | boolean (value : Bool)
  | integer (value : Int)
  | string (value : String)
  | bytes (value : ByteArray)
  | path (value : ByteArray)
  | number (lexical : ByteArray)
  | array (values : List Value)
  | object (fields : List (String × Value))

private def tagged (tag : Nat) (bytes : ByteArray) : ByteArray :=
  ByteArray.mk #[tag.toUInt8] ++ littleEndian 8 bytes.size ++ bytes

def encodeValue : Value → ByteArray
  | .null => ByteArray.mk #[0]
  | .boolean value => ByteArray.mk #[if value then 2 else 1]
  | .integer value =>
    let bytes := (toString value).toUTF8
    ByteArray.mk #[3] ++ littleEndian 4 bytes.size ++ bytes
  | .string value => tagged 4 value.toUTF8
  | .bytes value => tagged 5 value
  | .path value => tagged 6 value
  | .number lexical => tagged 9 lexical
  | .array values => values.foldl (fun bytes value => bytes ++ encodeValue value)
      (ByteArray.mk #[7] ++ littleEndian 4 values.length)
  | .object fields => fields.foldl (fun bytes field =>
      bytes ++ tagged 4 field.1.toUTF8 ++ encodeValue field.2)
      (ByteArray.mk #[8] ++ littleEndian 4 fields.length)
termination_by value => sizeOf value
decreasing_by
  all_goals
    simp only [Value.array.sizeOf_spec, Value.object.sizeOf_spec]
    have smaller := List.sizeOf_lt_of_mem ‹_ ∈ _›
    first
    | omega
    | cases field; simp only [Prod.mk.sizeOf_spec] at *; omega

def encodeResponse (status : Nat) (value : Value) : ByteArray :=
  let payload := encodeValue value
  responseMagic ++ littleEndian 4 status ++ littleEndian 4 0 ++
    littleEndian 8 payload.size ++ payload

private structure Cursor where
  bytes : ByteArray
  position : Nat := 0
  nodes : Nat := valueNodeMax

private def take (cursor : Cursor) (amount : Nat) : Except String (ByteArray × Cursor) := do
  if amount > cursor.bytes.size - cursor.position then throw "truncated host value"
  return (cursor.bytes.extract cursor.position (cursor.position + amount),
    { cursor with position := cursor.position + amount })

private def word (cursor : Cursor) (width : Nat) : Except String (Nat × Cursor) := do
  let (bytes, next) ← take cursor width
  return (fromLittleEndian bytes, next)

private def payload (cursor : Cursor) (width limit : Nat) : Except String (ByteArray × Cursor) := do
  let (size, cursor) ← word cursor width
  if size > limit then throw "host value payload exceeds its bound"
  take cursor size

private def integer? (bytes : ByteArray) : Option Int := do
  let text ← String.fromUTF8? bytes
  let value ← text.toInt?
  if toString value == text then some value else none

private def items (parse : Cursor → Except String (Value × Cursor)) :
    Nat → Cursor → List Value → Except String (List Value × Cursor)
  | 0, cursor, values => .ok (values.reverse, cursor)
  | count + 1, cursor, values => do
    let (value, next) ← parse cursor
    items parse count next (value :: values)

private def fields (parse : Cursor → Except String (Value × Cursor)) :
    Nat → Cursor → List (String × Value) → Except String (List (String × Value) × Cursor)
  | 0, cursor, values => .ok (values.reverse, cursor)
  | count + 1, cursor, values => do
    let (key, next) ← parse cursor
    let key ← match key with
      | .string key => pure key
      | _ => throw "host object key must be a string"
    if values.any (fun field => field.1 == key) then throw "duplicate host object key"
    let (value, next) ← parse next
    fields parse count next ((key, value) :: values)

-- §FS-host-boundary.caller: Depth and node budgets decrease independently of peer data.
private def parseValue : Nat → Cursor → Except String (Value × Cursor)
  | 0, _ => .error "host value depth exceeded"
  | depth + 1, cursor => do
    if cursor.nodes == 0 then throw "host value node budget exceeded"
    let cursor := { cursor with nodes := cursor.nodes - 1 }
    let (tag, cursor) ← word cursor 1
    match tag with
    | 0 => return (.null, cursor)
    | 1 => return (.boolean false, cursor)
    | 2 => return (.boolean true, cursor)
    | 3 =>
      let (bytes, cursor) ← payload cursor 4 32
      match integer? bytes with
      | some value => return (.integer value, cursor)
      | none => throw "noncanonical host integer"
    | 4 =>
      let (bytes, cursor) ← payload cursor 8 manifestMax
      match String.fromUTF8? bytes with
      | some value => return (.string value, cursor)
      | none => throw "invalid host string encoding"
    | 5 =>
      let (bytes, cursor) ← payload cursor 8 workspaceMax
      return (.bytes bytes, cursor)
    | 6 =>
      let (bytes, cursor) ← payload cursor 8 pathMax
      if bytes.data.toList.contains 0 then throw "NUL in returned filesystem path"
      return (.path bytes, cursor)
    | 7 =>
      let (count, cursor) ← word cursor 4
      if count > cursor.nodes then throw "host array exceeds node budget"
      let (values, cursor) ← items (parseValue depth) count cursor []
      return (.array values, cursor)
    | 8 =>
      let (count, cursor) ← word cursor 4
      if count > cursor.nodes / 2 then throw "host object exceeds node budget"
      let (values, cursor) ← fields (parseValue depth) count cursor []
      return (.object values, cursor)
    | 9 =>
      let (bytes, cursor) ← payload cursor 8 reportMax
      match Json.parse bytes reportMax with
      | .ok (.number lexical) =>
        if ByteArray.mk lexical.toArray != bytes then throw "noncanonical JSON-number wire bytes"
        return (.number bytes, cursor)
      | _ => throw "invalid JSON-number wire bytes"
    | _ => throw "unknown host value tag"

-- §FS-host-boundary.transport: Only one complete bounded response with no trailing bytes returns.
def decodeResponse (bytes : ByteArray) : Except String (Nat × Value) := do
  if bytes.size < responseHeader || bytes.size > responseHeader + responseMax ||
      bytes.extract 0 8 != responseMagic then throw "invalid host response header"
  let status := readWord bytes 8 4
  let reserved := readWord bytes 12 4
  let size := readWord bytes 16 8
  if status > 3 || reserved != 0 || size > responseMax || size != bytes.size - responseHeader then
    throw "inconsistent host response header"
  let (value, cursor) ← parseValue valueDepthMax { bytes, position := responseHeader }
  if cursor.position != bytes.size then throw "trailing host response bytes"
  return (status, value)

end LeanCage.Host.GatewayWire
