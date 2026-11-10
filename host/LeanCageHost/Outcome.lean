import LeanCageHost.Artifacts
import LeanCageHost.Validation

namespace LeanCage.Host
open Filesystem

structure Outcome where
  requestId : String
  bundleId : String
  command : String
  status : String
  report : Option Json.Value
  exitCode : Nat
  vmCleanup : String
  error : Option String
  stdout : ByteArray := .empty
  stderr : ByteArray := .empty
  files : List Artifacts.ValidatedFile := []
  output : Option ByteArray := none
  publication : String := "pending"
  publicationError : Option String := none

def optionalText (text : Option String) : GatewayWire.Value :=
  match text with
  | none => .null
  | some text => .string text

def Outcome.storageFailure (outcome : Outcome) (error : String) : Outcome :=
  { outcome with
    output := none
    publication := "failed"
    publicationError := some error
    exitCode := 126 }

def captureInfo (bytes digest : ByteArray) : GatewayWire.Value :=
  .object [("bytes", .integer (Int.ofNat bytes.size)), ("sha256", .string (Snapshot.hex digest))]

-- §FS-host-boundary.publication: The envelope preserves the report and its distinct outer facts.
def Outcome.metadata (outcome : Outcome) (stdoutHash stderrHash : ByteArray) : GatewayWire.Value :=
  let report := outcome.report.map Validation.jsonToWire |>.getD .null
  .object [
    ("schema", .string "leancage-workspace-v1"), ("request_id", .string outcome.requestId),
    ("bundle_id", .string outcome.bundleId), ("command", .string outcome.command),
    ("status", .string outcome.status), ("report", report),
    ("exit_code", .integer (Int.ofNat outcome.exitCode)), ("vm_cleanup", .string outcome.vmCleanup),
    ("error", optionalText outcome.error), ("publication", .string outcome.publication),
    ("publication_error", optionalText outcome.publicationError),
    ("output", outcome.output.map GatewayWire.Value.path |>.getD .null),
    ("artifacts", .object [
      ("complete", .boolean (outcome.status == "complete")),
      ("stdout", if outcome.status == "complete" then captureInfo outcome.stdout stdoutHash else .null),
      ("stderr", if outcome.status == "complete" then captureInfo outcome.stderr stderrHash else .null),
      ("files", .object (outcome.files.map (fun file =>
        (file.path.text, captureInfo file.bytes file.digest))))])]

def Outcome.wire (outcome : Outcome) (metadata : GatewayWire.Value) : GatewayWire.Value :=
  let report := outcome.report.map Validation.jsonToWire |>.getD .null
  .object [
    ("request_id", .string outcome.requestId), ("bundle_id", .string outcome.bundleId),
    ("command", .string outcome.command), ("status", .string outcome.status), ("report", report),
    ("exit_code", .integer (Int.ofNat outcome.exitCode)), ("vm_cleanup", .string outcome.vmCleanup),
    ("error", optionalText outcome.error), ("stdout", .bytes outcome.stdout),
    ("stderr", .bytes outcome.stderr),
    ("files", .object (outcome.files.map (fun file => (file.path.text, .bytes file.bytes)))),
    ("output", outcome.output.map GatewayWire.Value.path |>.getD .null),
    ("publication", .string outcome.publication),
    ("publication_error", optionalText outcome.publicationError), ("json", metadata)]

def Outcome.identify (outcome : Outcome) : Filesystem.Program (Filesystem.Result (ByteArray × ByteArray)) := do
  if outcome.status != "complete" then return .ok (.empty, .empty)
  let stdout ← Filesystem.hash outcome.stdout
  match stdout with
  | .error error => return .error error
  | .ok stdout =>
    let stderr ← Filesystem.hash outcome.stderr
    return stderr.map (fun stderr => (stdout, stderr))

end LeanCage.Host
