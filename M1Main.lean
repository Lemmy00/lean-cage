import LeanCage.Linux.Launch

open LeanCage.Linux

-- §FS-filter-loading.input.layout: Bound file reads at one byte beyond the rejection ceiling.
private def readFilter (path : System.FilePath) : IO ByteArray :=
  IO.FS.withFile path .read fun handle => do
    let mut bytes := ByteArray.empty
    while bytes.size < 32769 do
      let chunk ← handle.read (min 4096 (32769 - bytes.size)).toUSize
      if chunk.isEmpty then break
      bytes := bytes ++ chunk
    return bytes

-- §FS-filter-loading.installation.binding: Scoped VM demo executable, not the future sandbox CLI.
def main (args : List String) : IO UInt32 := do
  match args with
  | [filterPath, executable, modeText] =>
    try
      let some mode := modeText.toNat? | throw (IO.userError "invalid mode")
      if mode > 5 then throw (IO.userError "unsupported mode")
      let bytes ← readFilter filterPath
      match ← launch bytes executable mode.toUInt32 with
      | .error error =>
        IO.println s!"M1_RESULT kind=validation error={repr error}"
        return 64
      | .ok packed =>
        let kind := packed &&& 255
        let phase := (packed >>> 8) &&& 255
        let detail := (packed >>> 16) &&& 0xffffffff
        let receipts := (packed >>> 48) &&& 255
        IO.println s!"M1_RESULT kind={kind} phase={phase} detail={detail} receipts={receipts}"
        if kind == 0 then return detail.toUInt32
        else if kind == 2 then return 128 + detail.toUInt32
        else return 125
    catch _ =>
      IO.println "M1_RESULT kind=io_failure"
      return 65
  | _ =>
    IO.println "usage: leancage-m1 FILTER STATIC_ELF TEST_MODE"
    return 64
