import LeanCageHost.Artifacts.Types

namespace LeanCage.Host.Artifacts

open Filesystem

def stringField (value : Json.Value) (key : String) : Option String :=
  match Json.get? value key with
  | some (.string text) => some text
  | _ => none

def readString (value : Json.Value) (key : String) : Result String :=
  match stringField value key with
  | some text => .ok text
  | none => .error "missing or invalid report string"

def readNatural (value : Json.Value) (key : String) (maximum : Nat) : Result Nat :=
  match Json.get? value key |>.bind (fun field => Json.naturalBelow? field maximum) with
  | some number => .ok number
  | none => .error "missing or invalid report count"

def readOptionalNatural (value : Json.Value) (key : String) (maximum : Nat) : Result (Option Nat) :=
  match Json.get? value key with
  | some .null => .ok none
  | some field =>
    match Json.naturalBelow? field maximum with
    | some number => .ok (some number)
    | none => .error "invalid optional report count"
  | none => .error "missing optional report count"

def readOptionalBool (value : Json.Value) (key : String) : Result (Option Bool) :=
  match Json.get? value key with
  | some .null => .ok none
  | some (.bool boolean) => .ok (some boolean)
  | _ => .error "missing or invalid report boolean"

def readOptionalString (value : Json.Value) (key : String) : Result (Option String) :=
  match Json.get? value key with
  | some .null => .ok none
  | some (.string text) => .ok (some text)
  | _ => .error "missing or invalid optional report string"

def digestText (text : String) : Bool :=
  text.toUTF8.size == 64 && Transport.lowerHex text.toUTF8

def recognized (preflight : Bool) (value : Json.Value) : Bool :=
  stringField value "schema" == some "leancage-result-v1" &&
  (Json.get? value "run_id" |>.bind (fun field => Json.naturalBelow? field 1)).isSome &&
  (stringField value "entry").any (fun entry => entry == "no" || entry == "yes" || entry == "unknown") &&
  (stringField value "cleanup").any (fun cleanup => cleanup == "complete" || cleanup == "unknown") &&
  (!preflight || (stringField value "entry" == some "no" &&
    ((Json.get? value "run_id" |>.bind (fun field => Json.naturalBelow? field 1)) == some 0 ||
      stringField value "termination" == some "setup_failed")))

-- §FS-host-boundary.publication: Recognition preserves the decoded report without rewriting it.
def knownReport (preflight : Bool) (raw : ByteArray) : Option Json.Value :=
  match Json.parse raw reportMax with
  | .error _ => none
  | .ok value => if recognized preflight value then some value else none

-- §FS-host-boundary.artifacts: Missing, noncanonical, rounded and overflowing counts reject.
def reportFields (expected : Expected) (value : Json.Value) : Result Report := do
  let runId ← readNatural value "run_id" 1
  let stage ← readNatural value "stage" 9
  let detail ← readNatural value "detail" 4095
  let uid ← readNatural value "uid" 100999
  let cancellationBits ← readNatural value "cancellation_bits" 63
  let exportErrno ← readNatural value "export_errno" 4095
  let exportOmitted ← readNatural value "export_omitted" expected.limits.inodesMax
  let entry ← readString value "entry"
  let cleanup ← readString value "cleanup"
  let termination ← readString value "termination"
  let storage ← readString value "report_storage"
  let storageError ← readOptionalString value "report_storage_error"
  let exportState ← readString value "export"
  let exportDigest ← readOptionalString value "export_digest"
  let stdoutCaptured ← readOptionalNatural value "stdout_captured_bytes" expected.limits.stdoutMax
  let stderrCaptured ← readOptionalNatural value "stderr_captured_bytes" expected.limits.stderrMax
  let stdoutObserved ← readOptionalNatural value "stdout_bytes" (2^64 - 1)
  let stderrObserved ← readOptionalNatural value "stderr_bytes" (2^64 - 1)
  let stdoutTruncated ← readOptionalBool value "stdout_truncated"
  let stderrTruncated ← readOptionalBool value "stderr_truncated"
  return ⟨runId, stage, detail, uid, cancellationBits, exportErrno, exportOmitted, entry, cleanup,
    termination, storage, storageError, exportState, exportDigest, stdoutCaptured, stderrCaptured,
    stdoutObserved, stderrObserved, stdoutTruncated, stderrTruncated⟩

def Report.kindValid (expected : Expected) (report : Report) : Bool :=
  let identity := if report.runId == 0 then report.uid == 0 && report.entry == "no"
    else 100000 ≤ report.uid && report.uid ≤ 100999
  let kind := match report.termination with
    | "exited" => report.runId == 1 && report.stage == 0 && report.detail ≤ 255 && report.entry == "yes"
    | "signaled" => report.runId == 1 && report.stage == 0 && 1 ≤ report.detail &&
        report.detail ≤ 64 && report.entry == "yes"
    | "setup_failed" => 1 ≤ report.stage && report.stage ≤ 8 && 1 ≤ report.detail && report.entry == "no"
    | "cancelled" => report.runId == 1 && report.stage == 0 && report.detail == 0 && report.cancellationBits > 0
    | "unknown" => report.stage == 9 && 1 ≤ report.detail
    | "preflight_supported" => report.runId == 0 && report.stage == 0 && report.detail == 0 &&
        report.entry == "no" && report.cleanup == "complete" && report.cancellationBits == 0
    | _ => false
  identity && kind && (if expected.preflight then
    report.entry == "no" && (report.termination == "preflight_supported" || report.termination == "setup_failed")
    else report.termination != "preflight_supported")

def Report.exportValid (report : Report) : Bool :=
  match report.exportState, report.exportDigest with
  | "complete", some digest => digestText digest && report.exportErrno == 0
  | "discarded", none => report.exportErrno == 0
  | "failed", none | "unavailable", none => 1 ≤ report.exportErrno
  | _, _ => false

def Report.storageValid (expected : Expected) (report : Report) : Bool :=
  if expected.preflight || report.runId == 0 then report.storage == "not_applicable" && report.storageError.isNone
  else match report.storage, report.storageError with
    | "stored", none => true
    | "failed", some error => !error.isEmpty
    | _, _ => false

def captureConsistent (entry : String) (count : Option Nat) (content : Option ByteArray) (limit : Nat) : Bool :=
  content.all (fun bytes => bytes.size ≤ limit) &&
  match count, content with
  | none, _ => true
  | some count, some bytes => bytes.size == count
  | some count, none => count == 0 && entry != "yes"

def observedConsistent (observed captured : Option Nat) (truncated : Option Bool) (limit : Nat) : Bool :=
  match observed with
  | none => true
  | some observed => captured.all (fun count => count == min observed limit) &&
      truncated.all (fun flag => flag == decide (limit < observed))

def noArtifacts (received : Transport.Result) : Bool :=
  received.stored.isNone && received.stdout.isNone && received.stderr.isNone &&
    received.manifest.isNone && received.blobs.isEmpty

-- §FS-host-boundary.artifacts: Every run kind gets artifact and retrieval checks.
def checkControl (expected : Expected) (received : Transport.Result) (report : Report) : Result Unit := do
  if !report.kindValid expected || !report.exportValid || !report.storageValid expected then
    Except.error ("inconsistent typed report" : Failure)
  if received.terminal.error != 0 || received.terminal.controller > 255 ||
      received.terminal.retrieved > 255 || received.terminal.extinct > 1 then
    Except.error ("invalid completed transport status" : Failure)
  if report.cleanup == "complete" && received.terminal.extinct != 1 then
    Except.error ("cleanup report differs from terminal scope" : Failure)
  if !captureConsistent report.entry report.stdoutCaptured received.stdout expected.limits.stdoutMax ||
      !captureConsistent report.entry report.stderrCaptured received.stderr expected.limits.stderrMax ||
      !observedConsistent report.stdoutObserved report.stdoutCaptured report.stdoutTruncated expected.limits.stdoutMax ||
      !observedConsistent report.stderrObserved report.stderrCaptured report.stderrTruncated expected.limits.stderrMax then
    Except.error ("capture bytes differ from report" : Failure)
  if expected.preflight || report.runId == 0 then
    if !noArtifacts received || received.terminal.retrieved != 126 || report.exportState == "complete" then
      Except.error ("unallocated run returned workload artifacts" : Failure)
  else
    if report.storage == "stored" then
      if received.terminal.retrieved != 0 || received.stored != some received.report then
        Except.error ("stored report retrieval differs" : Failure)
    else if received.terminal.retrieved == 0 || received.stored.isSome then
      Except.error ("failed storage returned a stored report" : Failure)
    if report.exportState == "complete" then
      if received.manifest.isNone then Except.error ("missing committed export manifest" : Failure)
    else if received.manifest.isSome || !received.blobs.isEmpty then
      Except.error ("uncommitted export artifacts" : Failure)
  return ()

-- §FS-host-boundary.artifacts: Bind the typed checks to this same parsed raw report.
def checkReport (expected : Expected) (received : Transport.Result) : Result (Json.Value × Report) := do
  if !expected.limits.valid then Except.error ("unsupported artifact limits" : Failure)
  let value ← (Json.parse received.report reportMax).mapError (fun _ => ("invalid report JSON" : Failure))
  if !recognized expected.preflight value || stringField value "profile" != some expected.profile ||
      stringField value "runtime_manifest_digest" != some expected.runtimeDigest then
    Except.error ("report profile or run binding differs" : Failure)
  let report ← reportFields expected value
  checkControl expected received report
  return (value, report)

end LeanCage.Host.Artifacts
