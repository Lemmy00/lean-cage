import LeanCageHost.Snapshot

open LeanCage.Host LeanCage.Host.Filesystem

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def openDirectory (path : String) : IO UInt64 := do
  let reply ← rawCall {op := .openAt, first := cwd, second := directoryFlags, left := path.toUTF8}
  let some fd := descriptor reply | throw (IO.userError "cannot open the owned directory fixture")
  return fd

-- §AR-host-boundary.primitives: The actual valid cursor is tested with a different live
-- expected FD, an invalid-width FD, and then its original retained FD.
def main (arguments : List String) : IO UInt32 := do
  let [path] := arguments | IO.eprintln "expected FRESH_OWNED_DIRECTORY"; return 2
  let fd ← openDirectory path
  let guard ← openDirectory path
  let opened ← rawCall {op := .dirOpen, first := fd}
  require (opened.1 == 0 && opened.2.size == 8) "actual fdopendir failed"
  let cursor := (fromLittleEndian opened.2).toUInt64
  require (cursor != 0) "actual fdopendir returned a zero cursor"
  let wrong ← rawCall {op := .dirClose, first := cursor, second := guard}
  require (nativeError wrong && errorNumber wrong == 22 && wrong.2.isEmpty)
    "directory close admitted a different live descriptor"
  let oversized ← rawCall {op := .dirClose, first := cursor, second := 2147483648}
  require (nativeError oversized && errorNumber oversized == 22 && oversized.2.isEmpty)
    "directory close narrowed an out-of-range expected descriptor"
  let stillOpen ← rawCall {op := .stat, first := fd}
  let guardOpen ← rawCall {op := .stat, first := guard}
  require ((parseStat stillOpen).isSome && (parseStat guardOpen).isSome)
    "a rejected close retired one of the actual live descriptors"
  let closed ← rawCall {op := .dirClose, first := cursor, second := fd}
  require (closed.1 == 0 && closed.2.isEmpty) "the matching expected-FD close failed"
  let gone ← rawCall {op := .stat, first := fd}
  require (nativeError gone && errorNumber gone == 9) "the matching close left its descriptor live"
  let guarded ← rawCall {op := .stat, first := guard}
  require ((parseStat guarded).isSome) "the matching close retired the other live descriptor"
  let _ ← rawCall {op := .close, first := guard}
  IO.println "actual fdopendir/dirfd/closedir: mismatches denied; matching FD alone retired"
  return 0
