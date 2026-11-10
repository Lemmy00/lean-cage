import LeanCageHost.Publication.Types

namespace LeanCage.Host.Publication
open Filesystem

-- §FS-host-boundary.ownership: Retain each checked descendant until its exact operation returns.
def under {α : Type} : Nat → UInt64 → List String → Bool →
    (UInt64 → Filesystem.Program (Result α)) → Filesystem.Program (Result α)
  | _, fd, [], _, action => action fd
  | uid, fd, name :: rest, create, action =>
    if ¬ Snapshot.ValidComponent name then pure (.error "invalid relative artifact component")
    else do
      let opened ← if create then Directories.ensureAt uid fd name.toUTF8
        else Directories.openAt uid fd name.toUTF8
      match opened with
      | .error error => return .error error
      | .ok child => (under uid child.fd rest create action).bind (closeResult child.fd)

def writeRelative (uid : Nat) (root : UInt64) (file : Artifacts.ValidatedFile) :
    Filesystem.Program (Result Unit) := do
  let components := file.path.components
  let some name := components.getLast? | return .error "empty relative file name"
  under uid root components.dropLast false (fun parent =>
    writeNew parent name.toUTF8 file.bytes (if file.executable then 448 else 384))

def directories (uid : Nat) (root : UInt64) (paths : List Artifacts.ExportPath) :
    Filesystem.Program (Result Unit) := do
  for path in paths.mergeSort (fun a b => a.components.length ≤ b.components.length) do
    let made ← under uid root path.components true (fun _ => pure (.ok ()))
    if let .error error := made then return .error error
  return .ok ()

def exports (uid : Nat) (stage : UInt64) (input : Input) : Filesystem.Program (Result Unit) := do
  let made ← Filesystem.Program.effect {
    op := .mkdirAt, first := stage, second := 448, left := "export".toUTF8 }
  if made.1 != 0 || !made.2.isEmpty then return .error (failure "fresh export mkdirat" made)
  let opened ← Directories.openAt uid stage "export".toUTF8
  match opened with
  | .error error => return .error error
  | .ok root =>
    let filled ← (do
      let made ← directories uid root.fd (input.validated.map (·.dirs) |>.getD [])
      if let .error error := made then return .error error
      for file in input.outcome.files do
        let written ← writeRelative uid root.fd file
        if let .error error := written then return .error error
      return .ok ())
    closeResult root.fd filled

-- §FS-host-boundary.publication: Every content file is new beneath this retained private stage.
def fill (uid : Nat) (stage : UInt64) (input : Input) (json wire : ByteArray) :
    Filesystem.Program (Result Unit) := do
  if json.size > metadataMax || wire.size > metadataMax || input.policy.raw.size > reportMax ||
      input.boot.size > 4 * 1024 * 1024 then
    return .error "publication metadata exceeds its bound"
  let mut files := [("policy.json", input.policy.raw), ("boot.log", input.boot)]
  if let some raw := input.rawReport then
    if raw.size > reportMax then return .error "publication report exceeds its bound"
    files := files ++ [("vm-report.json", raw)]
  if input.outcome.status == "complete" then
    files := files ++ [("stdout", input.outcome.stdout), ("stderr", input.outcome.stderr)]
    if let some stored := input.validated.bind (·.stored) then
      files := files ++ [("stored-report.json", stored)]
    if let some manifest := input.validated.bind (·.manifest) then
      files := files ++ [("export.manifest", manifest)]
  files := files ++ [("result.json", json), ("publication.wire", wire)]
  for (name, bytes) in files do
    let written ← writeNew stage name.toUTF8 bytes
    if let .error error := written then return .error error
  exports uid stage input

def unlinkRelative (uid : Nat) (root : UInt64) (components : List String) (directory : Bool) :
    Filesystem.Program Unit := do
  if let some name := components.getLast? then
    let _ ← under uid root components.dropLast false (fun parent => do
      let reply ← Filesystem.Program.effect {
        op := .unlinkAt
        first := parent
        second := if directory then 512 else 0
        left := name.toUTF8 }
      if reply.1 == 0 && reply.2.isEmpty then return .ok ()
      return .error (failure "stage unlinkat" reply))
  pure ()

-- §FS-host-boundary.ownership: Failed stages release only their own planned descendants.
def cleanup (parent : Directories.Parent) (stage : Directories.Fresh) (input : Input) :
    Filesystem.Program Unit := do
  let root ← Directories.openAt parent.uid stage.directory.fd "export".toUTF8
  if let .ok root := root then
    for file in input.outcome.files do unlinkRelative parent.uid root.fd file.path.components false
    let dirs := input.validated.map (·.dirs) |>.getD []
    for path in dirs.mergeSort (fun a b => b.components.length ≤ a.components.length) do
      unlinkRelative parent.uid root.fd path.components true
    let _ ← Filesystem.Program.effect { op := .close, first := root.fd }
  for name in ["policy.json", "boot.log", "vm-report.json", "stdout", "stderr",
      "stored-report.json", "export.manifest", "result.json", "publication.wire"] do
    let _ ← Filesystem.Program.effect { op := .unlinkAt, first := stage.directory.fd, left := name.toUTF8 }
  let _ ← Filesystem.Program.effect {
    op := .unlinkAt, first := stage.directory.fd, second := 512, left := "export".toUTF8 }
  let _ ← Filesystem.Program.effect { op := .close, first := stage.directory.fd }
  let _ ← Filesystem.Program.effect {
    op := .unlinkAt, first := stage.container.fd, second := 512, left := stage.name }
  let _ ← Filesystem.Program.effect { op := .close, first := stage.container.fd }
  pure ()

end LeanCage.Host.Publication
