import LeanCageM2.Model

open LeanCage.Linux.Filter LeanCageM2

-- §FS-lifecycle.resources: Bound input before allocation and preserve deterministic M1 rejection.
private def readFilter (path : System.FilePath) : IO ByteArray :=
  IO.FS.withFile path .read fun handle => do
    let mut bytes := ByteArray.empty
    while bytes.size < 32769 do
      let chunk ← handle.read (min 4096 (32769 - bytes.size)).toUSize
      if chunk.isEmpty then break
      bytes := bytes ++ chunk
    return bytes

-- §AR-lifecycle.design: A decoded fixed tag controls a fresh helper; no native override of Lean.
def main (args : List String) : IO UInt32 := do
  match args with
  | [filterPath, executable, mode, argument] =>
    try
      let bytes ← readFilter filterPath
      match preparePlan nativeAbi bytes with
      | .error error =>
        IO.println s!"M2_VALIDATION error={repr error}"
        return 64
      | .ok operations =>
        let parent ← IO.Process.getPID
        let child ← IO.Process.spawn {
          cmd := "/leancage-m2-helper"
          args := #[String.join (operations.map Operation.wire), executable, mode, argument, toString parent]
          stdin := .inherit, stdout := .inherit, stderr := .inherit }
        return ← child.wait
    catch _ =>
      IO.println "M2_CONTROLLER outcome=unknown"
      return 126
  | _ =>
    IO.println "usage: leancage-m2 FILTER STATIC_ELF TEST_MODE GUEST_ARGUMENT"
    return 64
