import LeanCageHost.Files

open LeanCage.Host LeanCage.Host.Filesystem

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

-- §FS-host-boundary.snapshot: This owned fixture advances the SAME descriptor's
-- stream cursor before each actual positional read of the maintained copy.
def main (arguments : List String) : IO UInt32 := do
  let [path] := arguments | IO.eprintln "expected FRESH_OWNED_FILE"; return 2
  let expected ← IO.FS.readBinFile path
  require (expected.size > chunkMax) "fixture must exercise multiple read chunks"
  let opened ← rawCall {op := .openAt, first := cwd, second := readFlags, left := path.toUTF8}
  let some fd := descriptor opened | throw (IO.userError "cannot open owned fixture")
  try
    let first ← rawCall {op := .read, first := fd, second := 7}
    require (first.1 == 7 && first.2 == expected.extract 0 7) "ordinary stream read failed"
    let reads ← IO.mkRef 0
    let copied ← (copyOpened fd expected.size).interpret (fun request => do
      if request.op == .read then
        let cursor ← rawCall {op := .read, first := fd, second := 1}
        require (cursor.1 == 1 && cursor.2.size == 1) "owned cursor perturbation failed"
        reads.modify (· + 1)
      rawCall request)
    let .ok copied := copied | throw (IO.userError "maintained positional copy failed")
    require (copied.bytes == expected) "copy followed the shared cursor instead of its explicit offset"
    let count ← reads.get
    require (count ≥ 3) "fixture did not execute partial-copy chunks and EOF"
    let current ← rawCall {op := .read, first := fd, second := 1}
    require (current.1 == 1 && current.2 == expected.extract (7 + count) (8 + count))
      "positional reads changed the ordinary stream cursor"
    let invalid ← rawCall {op := .read, first := fd, second := 1, third := 9223372036854775809}
    require (nativeError invalid && errorNumber invalid == 75 && invalid.2.isEmpty)
      "out-of-range file offset was narrowed"
    IO.println s!"actual positional copy retained {copied.bytes.size} bytes across {count} cursor changes; overflow rejected"
    return 0
  finally
    let _ ← rawCall {op := .close, first := fd}
