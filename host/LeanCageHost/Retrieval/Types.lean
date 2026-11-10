import LeanCageHost.Publication

namespace LeanCage.Host.Retrieval

open Filesystem

def field (value : GatewayWire.Value) (key : String) : Option GatewayWire.Value :=
  match value with
  | .object fields => (fields.find? (fun entry => entry.1 == key)).map Prod.snd
  | _ => none

def stringField (value : GatewayWire.Value) (key : String) : Result String :=
  match field value key with
  | some (.string text) => .ok text
  | _ => .error "missing stored string"

def boolField (value : GatewayWire.Value) (key : String) : Result Bool :=
  match field value key with
  | some (.boolean flag) => .ok flag
  | _ => .error "missing stored boolean"

def naturalField (value : GatewayWire.Value) (key : String) (maximum : Nat) : Result Nat :=
  match field value key with
  | some (.integer (.ofNat number)) =>
    if number ≤ maximum then .ok number else .error "stored integer exceeds its bound"
  | _ => .error "missing stored natural integer"

def optionalString (value : GatewayWire.Value) (key : String) : Result (Option String) :=
  match field value key with
  | some .null => .ok none
  | some (.string text) => .ok (some text)
  | _ => .error "missing stored optional string"

def sameValue (first second : GatewayWire.Value) : Bool :=
  GatewayWire.encodeValue first == GatewayWire.encodeValue second

def requestId (text : String) : Bool :=
  text.toUTF8.size == 32 && Transport.lowerHex text.toUTF8

def publicOutcome (bundle : Validation.Bundle) (metadata : GatewayWire.Value) : Result Outcome := do
  if (← stringField metadata "schema") != "leancage-workspace-v1" then
    Except.error ("unsupported stored public schema" : Failure)
  let identity ← stringField metadata "request_id"
  let bundleId ← stringField metadata "bundle_id"
  let command ← stringField metadata "command"
  let status ← stringField metadata "status"
  if !requestId identity || bundleId != bundle.identity ||
      (command != "run" && command != "check") ||
      (status != "complete" && status != "incomplete") then
    Except.error ("stored request, bundle or command binding differs" : Failure)
  let exitCode ← naturalField metadata "exit_code" 255
  let cleanup ← stringField metadata "vm_cleanup"
  if cleanup != "complete" && cleanup != "unknown" && cleanup != "not_started" then
    Except.error ("unsupported stored VM cleanup observation" : Failure)
  let error ← optionalString metadata "error"
  if (← stringField metadata "publication") != "stored" ||
      (← optionalString metadata "publication_error").isSome then
    Except.error ("stored publication is not committed" : Failure)
  let some (.path output) := field metadata "output" | Except.error ("missing stored publication path" : Failure)
  if output.isEmpty || !rawPathValid output || output[0]! != 47 then
    Except.error ("invalid stored publication path" : Failure)
  return {
    requestId := identity
    bundleId
    command
    status
    report := none
    exitCode
    vmCleanup := cleanup
    error
    output := some output
    publication := "stored"
    publicationError := none }

def readTerminal (envelope : GatewayWire.Value) : Result (Option Transport.Terminal) := do
  match field envelope "terminal" with
  | some .null => return none
  | some (.object fields) =>
    let value := GatewayWire.Value.object fields
    return some ⟨← naturalField value "controller" 255, ← naturalField value "retrieved" 255,
      ← naturalField value "error" 4095, ← naturalField value "extinct" 1⟩
  | _ => Except.error ("invalid stored terminal observation" : Failure)

structure Envelope where
  metadata : GatewayWire.Value
  outcome : Outcome
  policyDigest : String
  reportPresent : Bool
  storedPresent : Bool
  manifestPresent : Bool
  stdoutPresent : Bool
  stderrPresent : Bool
  terminal : Option Transport.Terminal

-- §FS-host-boundary.publication: The signed envelope names these retained objects and final entry.
def decodeEnvelope (bytes : ByteArray) (bundle : Validation.Bundle)
    (parent : Directories.Parent) (target : Directories.Opened) : Result Envelope := do
  let .ok (0, .object fields) := GatewayWire.decodeResponse bytes
    | Except.error ("invalid stored typed envelope" : Failure)
  let envelope := GatewayWire.Value.object fields
  if (← stringField envelope "schema") != "leancage-publication-v1" then
    Except.error ("unsupported publication envelope schema" : Failure)
  if (← naturalField envelope "device" (2^64 - 1)) != target.information.device ||
      (← naturalField envelope "inode" (2^64 - 1)) != target.information.inode ||
      (← naturalField envelope "parent_device" (2^64 - 1)) != parent.directory.information.device ||
      (← naturalField envelope "parent_inode" (2^64 - 1)) != parent.directory.information.inode then
    Except.error ("stored publication object or parent identity differs" : Failure)
  let some (.path name) := field envelope "name" | Except.error ("missing publication entry name" : Failure)
  if name != parent.name then Except.error ("stored final publication name differs" : Failure)
  let digest ← stringField envelope "policy_sha256"
  if !Artifacts.digestText digest then Except.error ("invalid stored policy digest" : Failure)
  let some (.object fields) := field envelope "public" | Except.error ("missing stored public object" : Failure)
  let metadata := GatewayWire.Value.object fields
  let outcome ← publicOutcome bundle metadata
  let reportPresent ← boolField envelope "report_present"
  let storedPresent ← boolField envelope "stored_present"
  let manifestPresent ← boolField envelope "manifest_present"
  let stdoutPresent ← boolField envelope "stdout_present"
  let stderrPresent ← boolField envelope "stderr_present"
  let terminal ← readTerminal envelope
  if outcome.status == "complete" then
    if !reportPresent || terminal.isNone then Except.error ("complete publication lacks report or terminal" : Failure)
  else if storedPresent || manifestPresent || stdoutPresent || stderrPresent || terminal.isSome then
    Except.error ("incomplete publication claims complete artifacts" : Failure)
  return ⟨metadata, outcome, digest, reportPresent, storedPresent, manifestPresent,
    stdoutPresent, stderrPresent, terminal⟩

def expected (bundle : Validation.Bundle) (preflight : Bool) (limits : Transport.Limits) :
    Result Artifacts.Expected := do
  let some profile := Validation.stringField bundle.manifest "profile"
    | Except.error ("bundle profile is absent" : Failure)
  let some runtime := Validation.stringField bundle.manifest "runtime_manifest_digest"
    | Except.error ("bundle runtime identity is absent" : Failure)
  return ⟨preflight, profile, runtime, limits⟩

end LeanCage.Host.Retrieval
