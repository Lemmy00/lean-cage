import ImageProofs

open LeanCage.Host LeanCage.Host.Filesystem

-- §FS-host-boundary.snapshot: Exercise the actual archive writer with bounded partial replies.
private def check (label : String) (good : Bool) : IO Unit :=
  unless good do throw <| IO.userError ("image check failed: " ++ label)

private def overlay : List Image.Entry := [⟨"dir/é", 33024, "abc".toUTF8⟩]

def main : IO Unit := do
  check "useful bounded Unicode archive entry" (Image.overlayValid overlay)
  check "duplicate archive path rejects" (!Image.overlayValid (overlay ++ overlay))
  check "parent escape rejects" (!Image.overlayValid [⟨"../escape", 33024, .empty⟩])
  check "absolute archive name rejects" (!Image.overlayValid [⟨"/escape", 33024, .empty⟩])
  check "unsupported archive mode rejects" (!Image.overlayValid [⟨"file", 33279, .empty⟩])
  check "full32bit hexadecimal representation" (Image.hex8 4294967295 == "ffffffff")
  let captured ← IO.mkRef ByteArray.empty
  let result ← (Image.content 9 .empty overlay).interpret (fun request => do
    check "only retained output descriptor is written" (request.op == .write && request.first == 9)
    check "request bounded before reply" (0 < request.left.size && request.left.size ≤ chunkMax)
    let count := min 3 request.left.size
    captured.modify (· ++ request.left.extract 0 count)
    return (count.toUInt64, .empty))
  match result with
  | .error error => throw <| IO.userError error.message
  | .ok () => pure ()
  IO.FS.writeBinFile ".tools/host/image-proof/actual.cpio" (← captured.get)
  let config := Image.requestConfig (String.ofList (List.replicate 32 'a'))
    (String.ofList (List.replicate 64 'b')) true ⟨1, 2, 3, 4⟩ 2
  check "actual request config fixed ABI length" (config.size == 152)
  IO.FS.writeBinFile ".tools/host/image-proof/actual.config" config
  IO.println "Image checks passed: bounded partial writes, Unicode archive, duplicate/path/mode denial and exact config length."
