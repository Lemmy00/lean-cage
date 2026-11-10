import LeanCageHost.Publication

open LeanCage.Host
open LeanCage.Host.Filesystem

private def checked {α : Type} (result : Filesystem.Result α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error.message)

private def assertCase (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def outcome : Outcome := {
  requestId := "custody-fixture"
  bundleId := "owned-fixture"
  command := "run"
  status := "complete"
  report := some (.object [("fixture", .bool true)])
  exitCode := 0
  vmCleanup := "reaped"
  error := none }

private def commit (parent : Directories.Parent) (stage : Directories.Fresh) :
    Filesystem.Program (Filesystem.Result Outcome) := do
  let reply ← Filesystem.Program.effect {
    op := .renameNew
    first := stage.container.fd
    second := parent.directory.fd
    left := stage.name
    right := parent.name }
  Publication.finishCommit parent stage outcome reply

private def createPeer (stage : Directories.Fresh) : Filesystem.Program (Filesystem.Result Unit) := do
  let made ← Filesystem.Program.effect {
    op := .mkdirAt, first := stage.container.fd, second := 448, left := stage.name }
  if made.1 != 0 || !made.2.isEmpty then return .error (failure "fixture peer mkdir" made)
  let opened ← Directories.openAt stage.directory.information.uid stage.container.fd stage.name
  match opened with
  | .error error => return .error error
  | .ok peer =>
    let written ← writeNew peer.fd "peer".toUTF8 "peer remains".toUTF8
    closeResult peer.fd written

-- §FS-host-boundary.publication: The owned fixture commits on Linux, then changes only its ACK.
private def inject {α : Type} (lost : Bool) (stage : Directories.Fresh) :
    Filesystem.Program α → IO (Option α × List Op)
  | .pure value => pure (some value, [])
  | .call request next => do
    let actual ← Filesystem.call request
    if request.op == .renameNew then
      assertCase (actual.1 == 0 && actual.2.isEmpty) "fixture rename did not actually commit"
      checked (← Filesystem.execute (createPeer stage))
      if lost then return (none, [.renameNew])
      let rest ← inject lost stage (next (0 - 5, .empty))
      return (rest.1, request.op :: rest.2)
    else
      let rest ← inject lost stage (next actual)
      return (rest.1, request.op :: rest.2)

private def exercise (target : String) (lost : Bool) : IO Unit := do
  let parent ← checked (← Filesystem.execute (Directories.parent target.toUTF8 false))
  let stage ← checked (← Filesystem.execute (Directories.fresh parent))
  let retained ← checked (← Filesystem.execute
    (Directories.openAt parent.uid parent.directory.fd ".".toUTF8))
  checked (← Filesystem.execute (writeNew stage.directory.fd "kept".toUTF8 "committed".toUTF8))
  let (returned, calls) ← inject lost stage (commit parent stage)
  if lost then
    assertCase (returned.isNone && decide (calls = [.renameNew]))
      "a lost acknowledgement executed the continuation"
  else
    assertCase (decide (calls = [.renameNew, .close, .close, .close]))
      "a post-attempt branch performed more than the three owned closes"
    match returned with
    | some (.error error) => assertCase (error.errno == some 5) "error acknowledgement changed"
    | _ => throw (IO.userError "error acknowledgement was accepted as success")
  let committed ← checked (← Filesystem.execute
    (copyAt retained.fd (parent.name ++ "/kept".toUTF8) 64))
  let peer ← checked (← Filesystem.execute
    (copyAt retained.fd (stage.name ++ "/peer".toUTF8) 64))
  assertCase (committed.bytes == "committed".toUTF8) "committed content was removed"
  assertCase (peer.bytes == "peer remains".toUTF8) "a peer at the reused name was removed"
  let _ ← Filesystem.call { op := .close, first := retained.fd }
  if lost then
    let _ ← Filesystem.execute (Publication.closeOwned parent stage)
  IO.println (if lost then "actual rename + synthetic lost ACK: committed and reused-name contents retained"
    else "actual rename + synthetic error ACK: committed and reused-name contents retained")

-- §FS-host-boundary.acceptance: Arguments name two absent targets in a fresh owned fixture.
def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | [errorTarget, lostTarget] =>
    exercise errorTarget false
    exercise lostTarget true
    return 0
  | _ => IO.eprintln "expected two absent targets within a fresh owned test directory"; return 2
