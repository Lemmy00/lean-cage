import LeanCageHost.Retrieval.Types

namespace LeanCage.Host.Retrieval

open Filesystem

abbrev Checked (α : Type) := ExceptT Failure Filesystem.Program α

def filesystem {α : Type} (program : Filesystem.Program (Result α)) : Checked α :=
  ExceptT.mk program

def checked {α : Type} (result : Result α) : Checked α :=
  ExceptT.mk (pure result)

def reject {α : Type} (message : String) : Checked α :=
  checked (.error message)

def readFile (root : UInt64) (name : ByteArray) (limit : Nat) :
    Filesystem.Program (Result ByteArray) := do
  let copied ← copyAt root name limit
  return copied.map (·.bytes)

def optionalFile (root : UInt64) (name : ByteArray) (limit : Nat) (present : Bool) :
    Filesystem.Program (Result (Option ByteArray)) :=
  if present then do
    let read ← readFile root name limit
    return read.map some
  else pure (.ok none)

structure Collected where
  blobs : List Transport.Blob := []
  total : Nat := 0
  count : Nat := 0

-- §FS-host-boundary.publication: Every actual file is copied and hashed before deduplication.
def collect : Nat → UInt64 → Transport.Limits → List Artifacts.Node → Collected →
    Checked Collected
  | _, _, _, [], state => pure state
  | uid, root, limits, node :: rest, state => do
    if state.count ≥ limits.inodesMax then reject "retrieved export inode limit exceeded"
    else
      let count := state.count + 1
      match node with
      | .omitted _ => collect uid root limits rest { state with count := count }
      | .directory path =>
        let _ ← filesystem <| Publication.under uid root path.components false (fun _ => pure (.ok ()))
        collect uid root limits rest { state with count := count }
      | .file path executable size digest =>
        if state.total + size > limits.workspaceMax then
          reject "retrieved export aggregate limit exceeded before copying"
        else
          let some name := path.components.getLast? | reject "empty export file path"
          let copied ← filesystem <| Publication.under uid root path.components.dropLast false
            (fun parent => copyAt parent name.toUTF8 size)
          if copied.bytes.size != size || (copied.stat.mode &&& 73 != 0) != executable then
            reject "retrieved export size or executable flag differs"
          else
            let hashed ← filesystem (Filesystem.hash copied.bytes)
            if Snapshot.hex hashed != digest then reject "retrieved export content identity differs"
            else
              let blobs ← match state.blobs.find? (fun blob => blob.digest == digest.toUTF8) with
                | none => pure (⟨digest.toUTF8, copied.bytes⟩ :: state.blobs)
                | some before =>
                  if before.content == copied.bytes then pure state.blobs
                  else reject "retrieved export digest collision"
              collect uid root limits rest ⟨blobs, state.total + size, count⟩

-- §FS-host-boundary.publication: The complete checked manifest bounds traversal before retention.
def exportBlobs (uid : Nat) (stage : UInt64) (limits : Transport.Limits) (raw : ByteArray) :
    Filesystem.Program (Result (List Transport.Blob)) := do
  match Artifacts.parseManifest limits raw with
  | .error error => return .error error
  | .ok manifest =>
    let opened ← Directories.openAt uid stage "export".toUTF8
    match opened with
    | .error error => return .error error
    | .ok root =>
      let collected ← (collect uid root.fd limits manifest.entries.toList {}).run
      let closed ← closeResult root.fd collected
      return closed.map (·.blobs.reverse)

def manifestBlobs (uid : Nat) (stage : UInt64) (limits : Transport.Limits)
    (manifest : Option ByteArray) : Filesystem.Program (Result (List Transport.Blob)) :=
  match manifest with
  | none => pure (.ok [])
  | some manifest => exportBlobs uid stage limits manifest

def resultJson (root : UInt64) (metadata : GatewayWire.Value) :
    Filesystem.Program (Result Unit) := do
  match WireJson.render GatewayWire.valueDepthMax metadata with
  | .error error => return .error error
  | .ok expected =>
    if expected.size + 1 > Publication.metadataMax then return .error "stored JSON exceeds its bound"
    let actual ← readFile root "result.json".toUTF8 Publication.metadataMax
    return actual.bind (fun actual =>
      if actual == expected ++ "\n".toUTF8 then .ok ()
      else .error "stored public JSON differs from its typed envelope")

end LeanCage.Host.Retrieval
