import LeanCageHost.Directories

namespace LeanCage.Host.RunDirectory
open Filesystem

structure Owned where
  path : String
  directory : Directories.Opened
  container : Directories.Opened
  name : ByteArray

-- §FS-host-boundary.ownership: Create each run by an exclusive operation in its private anchor.
def create : Filesystem.Program (Result Owned) := do
  let area ← Directories.temporaryParent
  match area with
  | .error error => return .error error
  | .ok (container, areaPath, uid) =>
    let child ← Directories.newChild uid container.fd PrivateNames.prefixText
    match child with
    | .error error => closeResult container.fd (.error error)
    | .ok child =>
      let marked ← Filesystem.Program.effect {
        op := .setAttribute
        first := child.directory.fd
        left := PrivateNames.attributeName
        right := PrivateNames.attributeValue }
      if marked.1 != 0 || !marked.2.isEmpty then do
        let _ ← Filesystem.Program.effect { op := .close, first := child.directory.fd }
        let _ ← Filesystem.Program.effect {
          op := .unlinkAt, first := container.fd, second := 512, left := child.name }
        return ← closeResult container.fd (.error "private run marker failed")
      match String.fromUTF8? child.name with
      | none => do
        let _ ← Filesystem.Program.effect { op := .close, first := child.directory.fd }
        closeResult container.fd (.error "invalid private run name")
      | some name =>
        let path := areaPath ++ "/" ++ name
        if path.toUTF8.size + "/control.sock".toUTF8.size > 107 then do
          let _ ← Filesystem.Program.effect { op := .close, first := child.directory.fd }
          closeResult container.fd (.error "private run socket name exceeds its bound")
        else return .ok ⟨path, child.directory, container, child.name⟩

-- §FS-host-boundary.ownership: Release only these known children of the retained private run.
def cleanup (run : Owned) : Filesystem.Program Unit := do
  for name in ["request.cpio", "control.sock", "policy.json"] do
    let _ ← Filesystem.Program.effect {
      op := .unlinkAt, first := run.directory.fd, left := name.toUTF8 }
  let _ ← Filesystem.Program.effect { op := .close, first := run.directory.fd }
  let _ ← Filesystem.Program.effect {
    op := .unlinkAt, first := run.container.fd, second := 512, left := run.name }
  let _ ← Filesystem.Program.effect { op := .close, first := run.container.fd }
  pure ()

end LeanCage.Host.RunDirectory
