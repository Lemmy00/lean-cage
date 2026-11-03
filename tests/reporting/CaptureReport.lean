import LeanCageM3.API

open Lean LeanCageM3

-- §AR-workspace.transport: Actual C collector/encoder bytes go through the live decoder and API.
def main (args : List String) : IO Unit := do
  let [path, directory] := args | throw (IO.userError "expected frame and temporary directory")
  let bytes ← IO.FS.readBinFile path
  let result ← IO.ofExcept (decodeResult bytes)
  unless result.kind == 4 && result.triggers &&& 8 != 0 && result.stdoutBytes == 8 &&
      result.entry == .yes && result.clean do
    throw (IO.userError "collector failure facts were lost")
  let policy : Policy := ⟨#["/bin/sh"], none, none, false,
    ⟨16777216, 4, 100000, 100000, 10000, 100, 1048576, 64, 0, 8, 8⟩⟩
  let report := detailedReport result policy Json.null
  for key in ["stdout_bytes", "stderr_bytes", "stdout_captured_bytes", "stderr_captured_bytes",
      "stdout_truncated", "stderr_truncated"] do
    let value ← IO.ofExcept (report.getObjVal? key)
    unless value == Json.null do
      throw (IO.userError s!"lost capture was presented as complete: {key}")
  let saved : System.FilePath := directory ++ "/report.json"
  let stored ← persistReport saved report
  let retrieved ← IO.ofExcept (Json.parse (← IO.FS.readFile saved))
  unless retrieved == stored do throw (IO.userError "saved report differs")
  -- A second storage failure must preserve these independent observed facts too.
  let failed ← persistReport (directory ++ "/missing/report.json") report
  for key in ["entry", "termination", "cleanup", "cancellation_bits", "stdout_bytes",
      "stdout_captured_bytes", "stdout_truncated"] do
    let before ← IO.ofExcept (report.getObjVal? key)
    let after ← IO.ofExcept (failed.getObjVal? key)
    unless after == before do
      throw (IO.userError s!"publication changed observed field: {key}")
  let storage ← IO.ofExcept (failed.getObjValAs? String "report_storage")
  unless storage == "failed" do
    throw (IO.userError "failed publication was not recorded")
  IO.println "capture failure report preserved"
