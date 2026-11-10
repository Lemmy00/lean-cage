import LeanCageHost.SourcePaths

open LeanCage.Host
open LeanCage.Host.Filesystem

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def simulated : List Reply → Filesystem.Program Reply → Except String (Reply × List Request)
  | _, .pure result => .ok (result, [])
  | [], .call _ _ => .error "fixture exhausted the prescribed observations"
  | reply :: rest, .call request next => do
    let (result, requests) ← simulated rest (next reply)
    return (result, request :: requests)

private def sample (width value : Nat) : Reply := (0, littleEndian width value)

-- §FS-host-boundary.lookup: Synthetic observations exercise denial before any namespace syscall.
private def synthetic : IO Unit := do
  let primary : Request := { op := .mkdirAt, first := 10, second := 448, left := "fresh".toUTF8 }
  for flags in [Lookup.casefoldFlag, Lookup.encryptionFlag] do
    match simulated [sample 8 Lookup.extMagic, sample 4 flags] (guardedCall primary) with
    | .error message => throw (IO.userError message)
    | .ok (result, requests) =>
      require (result == Lookup.unsupported && requests.map (·.op) == [.filesystemType, .inodeFlags])
        "a prohibited directory flag reached namespace mutation"
      require (requests.all (fun request => request.first == 10)) "probe changed the retained FD"
  match simulated [sample 8 0] (guardedCall primary) with
  | .error message => throw (IO.userError message)
  | .ok (result, requests) =>
    require (result == Lookup.unsupported && requests.map (·.op) == [.filesystemType])
      "an unknown filesystem reached namespace mutation"
  match simulated [sample 8 Lookup.extMagic, sample 8 0] (guardedCall primary) with
  | .error message => throw (IO.userError message)
  | .ok (result, requests) =>
    require (result == Lookup.unsupported && requests.map (·.op) == [.filesystemType, .inodeFlags])
      "a malformed flag width was accepted"
  let directory : Request := { op := .openAt, first := cwd, second := directoryFlags, left := "/".toUTF8 }
  match simulated [(20, .empty), sample 8 0, (0, .empty)] (guardedCall directory) with
  | .error message => throw (IO.userError message)
  | .ok (result, requests) =>
    require (result == Lookup.unsupported && requests.map (·.op) == [.openAt, .filesystemType, .close])
      "post-open rejection erased the open or its close"
    require (requests.getLast? == some { op := .close, first := 20 })
      "rejection closed a descriptor other than the new one"
  let rename : Request := {
    op := .renameNew
    first := 10
    second := 11
    left := "stage".toUTF8
    right := "target".toUTF8 }
  match simulated [sample 8 Lookup.tmpMagic, sample 8 Lookup.extMagic,
      sample 4 Lookup.casefoldFlag] (guardedCall rename) with
  | .error message => throw (IO.userError message)
  | .ok (result, requests) =>
    require (result == Lookup.unsupported && requests.map (·.op) ==
      [.filesystemType, .filesystemType, .inodeFlags]) "rename skipped its destination-parent guard"
    require (requests.map (·.first) == [10, 11, 11]) "rename probes used another directory"
  IO.println "synthetic unknown/casefold/encryption/malformed/post-open/second-rename denials passed"

private def recorded {α : Type} : Filesystem.Program α → IO (α × List Request)
  | .pure value => pure (value, [])
  | .call request next => do
    let reply ← rawCall request
    let (value, rest) ← recorded (next reply)
    return (value, request :: rest)

private def useful (path : String) : IO Unit := do
  let opened ← Filesystem.execute (SourcePaths.open path.toUTF8 true)
  let fd ← match opened with
    | .ok fd => pure fd
    | .error error => throw (IO.userError error.message)
  let primary : Request := {
    op := .openAt
    first := fd
    second := newFileFlags
    third := 384
    left := "filesystem-access-fixture".toUTF8 }
  let (opened, requests) ← recorded (guardedCall primary)
  let some output := descriptor opened | throw (IO.userError "useful guarded exclusive open failed")
  require (requests.getLast? == some primary) "the useful trace lost the actual exclusive open"
  let written ← Filesystem.execute (writeLoop 8 output "retained bytes".toUTF8 0)
  let written ← Filesystem.execute (closeResult output written)
  if let .error error := written then throw (IO.userError error.message)
  let copied ← Filesystem.execute (copyAt fd "filesystem-access-fixture".toUTF8 64)
  match copied with
  | .error error => throw (IO.userError error.message)
  | .ok copied => require (copied.bytes == "retained bytes".toUTF8) "copied bytes differ"
  let removed ← call { op := .unlinkAt, first := fd, left := "filesystem-access-fixture".toUTF8 }
  require (removed.1 == 0 && removed.2.isEmpty) "owned fixture cleanup failed"
  let _ ← call { op := .close, first := fd }
  IO.println "actual supported filesystem: exclusive create/copy/remove kept exact bytes and probe trace"

-- §FS-host-boundary.acceptance: Casefold configuration is supplied only by the disposable VM.
private def casefoldDenied (path : String) : IO Unit := do
  let opened ← rawCall { op := .openAt, first := cwd, second := directoryFlags, left := path.toUTF8 }
  let some fd := descriptor opened | throw (IO.userError "cannot open the VM casefold fixture")
  let magic ← rawCall { op := .filesystemType, first := fd }
  let flags ← rawCall { op := .inodeFlags, first := fd }
  require (Lookup.word? 8 magic == some Lookup.extMagic) "fixture is not on the ext filesystem family"
  let some flags := Lookup.word? 4 flags | throw (IO.userError "fixture inode flags unavailable")
  require ((flags &&& Lookup.casefoldFlag) != 0) "fixture is not actually casefold enabled"
  let rename : Request := {
    op := .renameNew
    first := fd
    second := fd
    left := ".leancage-private-alias".toUTF8
    right := "visible".toUTF8 }
  let (denied, requests) ← recorded (guardedCall rename)
  require (denied == Lookup.unsupported && requests.map (·.op) == [.filesystemType, .inodeFlags])
    "actual casefold parent reached the rename syscall"
  let _ ← rawCall { op := .close, first := fd }
  let selected ← Filesystem.execute (SourcePaths.open path.toUTF8 true)
  match selected with
  | .ok fd =>
    let _ ← call { op := .close, first := fd }
    throw (IO.userError "caller traversal admitted an actual casefold directory")
  | .error error => require (error.errno == some 95) "casefold rejection changed its typed error"
  let alias ← Filesystem.execute (SourcePaths.copyFile
    (path ++ "/.LEANCAGE-PRIVATE-alias/secret").toUTF8 64)
  match alias with
  | .ok _ => throw (IO.userError "caller read entered the actual casefold private-stage alias")
  | .error error => require (error.errno == some 95) "casefold alias read changed its typed error"
  IO.println "actual disposable-VM casefold: caller alias read denied; no rename syscall reached"

private def unsupportedDenied (path : String) : IO Unit := do
  let opened ← rawCall { op := .openAt, first := cwd, second := directoryFlags, left := path.toUTF8 }
  let some fd := descriptor opened | throw (IO.userError "cannot open the unsupported VM fixture")
  let magic ← rawCall { op := .filesystemType, first := fd }
  let _ ← rawCall { op := .close, first := fd }
  let some magic := Lookup.word? 8 magic | throw (IO.userError "fixture filesystem type unavailable")
  require (magic != Lookup.extMagic && magic != Lookup.tmpMagic) "fixture filesystem is supported"
  let selected ← Filesystem.execute (SourcePaths.open path.toUTF8 true)
  match selected with
  | .ok fd =>
    let _ ← call { op := .close, first := fd }
    throw (IO.userError "caller traversal admitted an unsupported filesystem")
  | .error error => require (error.errno == some 95) "unsupported filesystem changed its typed error"
  IO.println "actual disposable-VM unsupported filesystem rejected by caller traversal"

def main (arguments : List String) : IO UInt32 := do
  synthetic
  match arguments with
  | ["useful", path] => useful path; return 0
  | ["casefold", path] => casefoldDenied path; return 0
  | ["unsupported", path] => unsupportedDenied path; return 0
  | [] => return 0
  | _ => IO.eprintln "expected useful FRESH_OWNED_DIRECTORY, casefold VM_DIRECTORY, or unsupported VM_DIRECTORY"; return 2
