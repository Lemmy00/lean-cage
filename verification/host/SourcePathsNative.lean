import LeanCageHost.SourcePaths
import LeanCageHost.Directories

open LeanCage.Host
open LeanCage.Host.Filesystem

-- §FS-host-boundary.ownership: Exercise retained relative selection after its pathname moves.
def exercise : Filesystem.Program (Filesystem.Result Unit) := do
  let selected ← SourcePaths.start "input".toUTF8
  match selected with
  | .error error => return .error error
  | .ok selected =>
    let parentReply ← Filesystem.Program.effect {
      op := .openAt, first := cwd, second := directoryFlags, left := "..".toUTF8 }
    let some parent := descriptor parentReply
      | closeResult selected.base (.error "cannot retain test parent")
    let moved ← Filesystem.Program.effect {
      op := .renameNew, first := parent, second := parent,
      left := "active".toUTF8, right := "moved".toUTF8 }
    if moved.1 != 0 || !moved.2.isEmpty then
      return ← closeResult parent (.error (failure "test move" moved))
    let made ← Filesystem.Program.effect {
      op := .mkdirAt, first := parent, second := 448, left := "active".toUTF8 }
    if made.1 != 0 || !made.2.isEmpty then
      return ← closeResult parent (.error (failure "test replacement" made))
    let replacement ← Filesystem.Program.effect {
      op := .openAt, first := parent, second := directoryFlags, left := "active".toUTF8 }
    let some replacement := descriptor replacement
      | closeResult parent (.error "cannot retain test replacement")
    let written ← writeNew replacement "input".toUTF8 "replacement".toUTF8
    let written ← closeResult replacement written
    match written with
    | .error error => return ← closeResult parent (.error error)
    | .ok () =>
      let source ← SourcePaths.walk selected.base selected.parts false
      match source with
      | .error error => return ← closeResult parent (.error error)
      | .ok source =>
        let copied ← (copyOpened source 64).bind (closeResult source)
        match copied with
        | .error error => return ← closeResult parent (.error error)
        | .ok copied =>
          if copied.bytes != "original".toUTF8 then
            return ← closeResult parent (.error "relative input followed a replacement pathname")
          let decoy ← copyAt parent "active/input".toUTF8 64
          match decoy with
          | .error error => return ← closeResult parent (.error error)
          | .ok decoy =>
            closeResult parent (if decoy.bytes == "replacement".toUTF8 then .ok ()
              else .error "test replacement was not exercised")

def main : IO UInt32 := do
  match ← Filesystem.execute exercise with
  | .ok () => IO.println "retained directory selected original input after ancestor rename"; return 0
  | .error error => IO.eprintln error.message; return 1
