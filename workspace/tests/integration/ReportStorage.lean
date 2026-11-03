import LeanCageM3.API

open Lean LeanCageM3

-- §AR-workspace.transport: Exercise real file errors with synthetic observations, without a guest.
def main (args : List String) : IO Unit := do
  let [path, report] := args | throw (IO.userError "expected path and observed report")
  let observed ← IO.ofExcept (Json.parse report)
  IO.println (← persistReport path observed).compress
