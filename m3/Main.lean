import LeanCageM3.API
import LeanCageM3.Filter

open Lean LeanCageM3

-- §FS-compatibility.interface: Real policy validation and private helper execution; VM-only
-- profile.
def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["validate-policy", path] =>
      match decodePolicy (← readBounded path 65536) with
      | .ok _ => IO.println "valid policy"; return 0
      | .error error => IO.println error; return 64
    | ["emit-filter", path] =>
      IO.FS.writeBinFile path Filter.bytes
      return 0
    | ["check", path] | ["run", path] =>
      let check := args.head? == some "check"
      match decodePolicy (← readBounded path 65536) with
      | .error error =>
        IO.println (Json.mkObj [("termination", "rejected"), ("entry", "no"), ("error", toJson error)]).compress
        return 64
      | .ok policy =>
        match ← invoke policy check with
        | .error error =>
          IO.println (Json.mkObj [("termination", "unknown"), ("entry", "unknown"),
            ("cleanup", "unknown"), ("error", toJson error)]).compress
          return 126
        | .ok (result, report) =>
          IO.println report.compress
          return if result.kind == 0 then result.detail.toUInt32 else if result.kind == 7 then 0
            else if result.kind == 2 then (128 + result.detail).toUInt32 else if result.kind == 3 then 124
            else if result.kind == 4 then 126 else 125
    | ["report", id] =>
      match id.toNat? with
      | none => return 64
      | some run =>
        if toString run != id || run == 0 || run > 18446744073709551615 then return 64
        let bytes ← readBounded s!"/m3-results/{run}/report.json" 65536
        if bytes.size > 65536 then return 126
        let some text := String.fromUTF8? bytes | return 126
        IO.println text
        return 0
    | _ =>
      IO.println "usage: leancage check POLICY | run POLICY | report RUN_ID"
      return 64
  catch error =>
    IO.println (Json.mkObj [("termination", "unknown"), ("entry", "unknown"),
      ("cleanup", "unknown"), ("error", toJson error.toString)]).compress
    return 126
