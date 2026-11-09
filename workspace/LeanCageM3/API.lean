import LeanCageM3.Results
import LeanCageM3.Metadata

namespace LeanCageM3
open Lean

-- §FS-metadata.bounds: Interpret the shared bounded open/read/close program.
def readBounded (path : System.FilePath) (limit : Nat) : IO ByteArray :=
  Metadata.readBounded path limit

def planArgs (policy : Policy) (parentPid : Nat) (preflight : Bool) : Array String :=
  let l := policy.limits
  #[if preflight then "M3CHECK1" else "M3PLAN1", toString l.memory, toString l.tasks,
    toString l.quota, toString l.cpu, toString l.wall, toString l.workspace,
    toString l.inodes, toString l.stdin, toString l.stdout, toString l.stderr, toString parentPid,
    if policy.exportFiles then "regular-files" else "discard",
    policy.workspaceInput.map (fun s => (s.drop 7).toString) |>.getD "none",
    policy.stdinInput.map (fun s => (s.drop 7).toString) |>.getD "none"] ++ policy.argv

-- §FS-workspace.results: Observation counts, stored prefixes and sampled overshoot have distinct
-- units.
def detailedReport (r : Result) (p : Policy) (identity : Json) : Json :=
  let fields := (r.json.getObj?.toOption.map (·.toList)).getD []
  Json.mkObj (fields ++ [
    ("accounting", toJson (if r.triggers &&& 16 != 0 then "unknown" else "complete")),
    ("identity", identity), ("assurance_artifact", toJson "/m3-assurance.json"),
    ("stdout_captured_bytes", if r.kind == 4 && r.triggers &&& 8 != 0 then Json.null else toJson (min r.stdoutBytes p.limits.stdout)),
    ("stderr_captured_bytes", if r.kind == 4 && r.triggers &&& 8 != 0 then Json.null else toJson (min r.stderrBytes p.limits.stderr)),
    ("stdout_truncated", if r.kind == 4 && r.triggers &&& 8 != 0 then Json.null else toJson (decide (r.stdoutBytes > p.limits.stdout))),
    ("stderr_truncated", if r.kind == 4 && r.triggers &&& 8 != 0 then Json.null else toJson (decide (r.stderrBytes > p.limits.stderr))),
    ("cpu_budget_us", toJson p.limits.cpu),
    ("cpu_observed_overshoot_us", if r.triggers &&& 16 != 0 then Json.null else toJson (r.cpu - p.limits.cpu)),
    ("wall_time_ms", toJson p.limits.wall),
    ("wall_observed_overshoot_ms", if r.triggers &&& 16 != 0 then Json.null else toJson (r.elapsed - p.limits.wall)),
    ("memory_semantics", toJson "Linux cgroup charged memory; transient excess and preloaded charges excluded"),
    ("poll_target_ms", toJson (10 : Nat))])

-- §FS-workspace.results: Storage failure must not erase facts from an authenticated result.
def reportStorage (report : Json) (status : String) (error : Option String := none) : Json :=
  Json.mkObj ((report.getObj?.toOption.map (·.toList)).getD [] ++ [
    ("report_storage", toJson status),
    ("report_storage_error", error.map toJson |>.getD Json.null)])

-- §AR-workspace.transport: Only a complete report is published in the trusted result directory.
def persistReport (path : System.FilePath) (report : Json) : IO Json := do
  let stored := reportStorage report "stored"
  let temporary : System.FilePath := path.toString ++ ".tmp"
  try
    IO.FS.writeFile temporary stored.compress
    IO.FS.rename temporary path
    return stored
  catch error =>
    try IO.FS.removeFile temporary catch _ => pure ()
    return reportStorage report "failed" (some error.toString)

-- §AR-workspace.transport: Only the helper's private stdout is decoded; guest bytes are separate
-- artifacts.
def invoke (policy : Policy) (preflight : Bool) : IO (Except String (Result × Json)) := do
  let marker ← readBounded "/leancage-m3-disposable-vm" 64
  if marker != "LeanCage-M3-root-VM-v1".toUTF8 then
    return .error "unsupported environment: this profile requires the designated disposable VM"
  let parentPid ← IO.Process.getPID
  let child ← IO.Process.spawn {
    cmd := "/leancage-m3-helper"
    args := planArgs policy parentPid.toNat preflight
    inheritEnv := false, env := #[("LC_ALL", some "C")], stdin := .null, stdout := .piped, stderr := .null }
  let mut bytes := ByteArray.empty
  while bytes.size ≤ 160 do
    let part ← child.stdout.read (161 - bytes.size).toUSize
    if part.isEmpty then break
    bytes := bytes ++ part
  let _ ← child.wait
  match decodeResult bytes with
  | .error error => return .error error
  | .ok result =>
    if preflight != (result.kind == 7) && result.kind != 1 then
      return .error "unexpected private result kind"
    let identity ← if result.run > 0 then do
      try
        let identityBytes ← readBounded s!"/m3-results/{result.run}/identity.json" 4096
        pure (if identityBytes.size > 4096 then Json.null else
          ((String.fromUTF8? identityBytes).bind (fun text => (Json.parse text).toOption)).getD Json.null)
      catch _ => pure Json.null
      else pure Json.null
    let observed := detailedReport result policy identity
    let report ← if !preflight && result.run > 0 then
      persistReport s!"/m3-results/{result.run}/report.json" observed
      else pure (reportStorage observed "not_applicable")
    return .ok (result, report)

end LeanCageM3
