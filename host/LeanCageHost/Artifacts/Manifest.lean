import LeanCageHost.Artifacts.Types

namespace LeanCage.Host.Artifacts

open Filesystem

-- §FS-host-boundary.artifacts: A line holds one bounded path, decimal size and digest.
def lineMax : Nat := 8350

def nibble (byte : UInt8) : Option Nat :=
  if 48 ≤ byte.toNat ∧ byte.toNat ≤ 57 then some (byte.toNat - 48)
  else if 97 ≤ byte.toNat ∧ byte.toNat ≤ 102 then some (byte.toNat - 87)
  else none

def unhexLoop : List UInt8 → ByteArray → Result ByteArray
  | [], bytes => .ok bytes
  | first :: second :: rest, bytes =>
    match nibble first, nibble second with
    | some high, some low => unhexLoop rest (bytes.push (UInt8.ofNat (16 * high + low)))
    | _, _ => .error "noncanonical hexadecimal export field"
  | _, _ => .error "odd hexadecimal export field"

def decodePath (encoded : ByteArray) : Result ExportPath := do
  if encoded.size == 0 || encoded.size > 8190 || encoded.size % 2 != 0 then
    Except.error ("export path encoding exceeds supported bounds" : Failure)
  let raw ← unhexLoop encoded.data.toList .empty
  if (Snapshot.hex raw).toUTF8 != encoded then Except.error ("noncanonical export path encoding" : Failure)
  let some text := String.fromUTF8? raw | Except.error ("export path is not supported UTF-8" : Failure)
  if text.toUTF8 != raw then Except.error ("export path UTF-8 identity differs" : Failure)
  if valid : ValidPath text then return ⟨text, valid⟩
  else Except.error ("unsupported export path" : Failure)

inductive NodeKind where
  | directory | file | omitted
  deriving DecidableEq, BEq, Repr

inductive Node where
  | directory (path : ExportPath)
  | file (path : ExportPath) (executable : Bool) (size : Nat) (digest : String)
  | omitted (path : ExportPath)

def Node.path : Node → ExportPath
  | .directory path | .file path _ _ _ | .omitted path => path

def Node.kind : Node → NodeKind
  | .directory _ => .directory
  | .file _ _ _ _ => .file
  | .omitted _ => .omitted

def Node.size : Node → Nat
  | .file _ _ size _ => size
  | _ => 0

-- §FS-host-boundary.artifacts: Stop before retaining a sixth token in a bounded line.
def splitFields : Nat → List UInt8 → ByteArray → List ByteArray → Result (List ByteArray)
  | 0, _, _, _ => .error "export line parsing made no bounded progress"
  | _ + 1, [], current, reversed => .ok (current :: reversed).reverse
  | fuel + 1, byte :: rest, current, reversed =>
    if byte = 32 then
      if reversed.length ≥ 4 then .error "too many export fields"
      else splitFields fuel rest .empty (current :: reversed)
    else splitFields fuel rest (current.push byte) reversed

def parseLine (limits : Transport.Limits) (line : ByteArray) : Result Node := do
  if line.size > lineMax then Except.error ("export line exceeds supported bounds" : Failure)
  let fields ← splitFields (line.size + 1) line.data.toList .empty []
  match fields with
  | [tag, encoded] =>
    let path ← decodePath encoded
    if tag = "D".toUTF8 then return .directory path
    else if tag = "O".toUTF8 then return .omitted path
    else Except.error ("invalid export entry tag" : Failure)
  | [tag, executable, encoded, count, digest] =>
    if tag != "F".toUTF8 || (executable != "0".toUTF8 && executable != "1".toUTF8) then
      Except.error ("invalid export file flags" : Failure)
    let path ← decodePath encoded
    let some size := Json.naturalTokenBelow? count.data.toList limits.workspaceMax
      | Except.error ("noncanonical or oversized export file count" : Failure)
    if digest.size != 64 || !Transport.lowerHex digest then Except.error ("invalid export file digest" : Failure)
    let some text := String.fromUTF8? digest | Except.error ("invalid export digest encoding" : Failure)
    if text.toUTF8 != digest then Except.error ("export digest identity differs" : Failure)
    return .file path (executable == "1".toUTF8) size text
  | _ => Except.error ("invalid export entry field count" : Failure)

structure ManifestState where
  entries : Array Node := #[]
  kinds : Std.TreeMap String NodeKind compare := ∅
  total : Nat := 0
  omitted : Nat := 0

def appendNode (limits : Transport.Limits) (state : ManifestState) (node : Node) : Result ManifestState :=
  if state.entries.size + 1 > limits.inodesMax then .error "export inode limit exceeded"
  else if state.total + node.size > limits.workspaceMax then .error "export aggregate byte limit exceeded"
  else if state.kinds.contains node.path.text then .error "duplicate export path"
  else .ok {
    entries := state.entries.push node
    kinds := state.kinds.insert node.path.text node.kind
    total := state.total + node.size
    omitted := state.omitted + (if node.kind = .omitted then 1 else 0)
  }

-- §FS-host-boundary.artifacts: Scan bytes with fuel and reject bounds before line/list retention.
def scanManifest : Nat → Transport.Limits → ByteArray → Nat → ByteArray → ManifestState → Result ManifestState
  | 0, _, _, _, _, _ => .error "export parsing made no bounded progress"
  | fuel + 1, limits, bytes, offset, current, state =>
    if offset < bytes.size then
      let byte := bytes[offset]!
      if byte = 10 then
        if state.entries.size ≥ limits.inodesMax then .error "export inode limit exceeded before entry"
        else do
          let node ← parseLine limits current
          let next ← appendNode limits state node
          scanManifest fuel limits bytes (offset + 1) .empty next
      else if current.size ≥ lineMax then .error "export line exceeds supported bounds"
      else scanManifest fuel limits bytes (offset + 1) (current.push byte) state
    else if current.isEmpty then .ok state
    else .error "truncated export manifest line"

def hierarchy (state : ManifestState) : Bool :=
  state.entries.toList.all (fun node => node.path.parents.all fun parent =>
    decide (state.kinds[parent]? = some .directory))

def parseManifest (limits : Transport.Limits) (bytes : ByteArray) : Result ManifestState := do
  if bytes.size > manifestMax || bytes.extract 0 10 != "LCEXPORT1\n".toUTF8 then
    Except.error ("invalid export manifest format or size" : Failure)
  let state ← scanManifest (bytes.size + 1) limits bytes 10 .empty {}
  if !hierarchy state then Except.error ("missing or conflicting export parent directory" : Failure)
  return state

def ManifestState.dirs (state : ManifestState) : List ExportPath :=
  state.entries.toList.filterMap (fun node => match node with | .directory path => some path | _ => none)

def ManifestState.omittedPaths (state : ManifestState) : List ExportPath :=
  state.entries.toList.filterMap (fun node => match node with | .omitted path => some path | _ => none)

end LeanCage.Host.Artifacts
