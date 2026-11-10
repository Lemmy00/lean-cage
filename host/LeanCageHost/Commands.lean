import LeanCageHost.Application
import LeanCageHost.Cli

namespace LeanCage.Host.Commands

def failureValue (failure : Filesystem.Failure) : Nat × GatewayWire.Value :=
  match failure.errno with
  | none => (1, .string failure.message)
  | some number => (2, .object [("message", .string failure.message),
      ("errno", .integer (Int.ofNat number))])

def dispatch (request : GatewayWire.Request) (duration : Option Nat := none) :
    Program (Nat × GatewayWire.Value) := do
  let result ← execute request duration
  match result with
  | .error failure => return failureValue failure
  | .ok value => return (0, value)

def cliResponse (code : Nat) (stdout : ByteArray) (stderr : ByteArray := .empty) :
    Nat × GatewayWire.Value :=
  (0, .object [("exit_code", .integer (Int.ofNat code)),
    ("stdout", .bytes stdout), ("stderr", .bytes stderr)])

def field (value : GatewayWire.Value) (key : String) : Option GatewayWire.Value :=
  match value with
  | .object fields => (fields.find? (fun field => field.1 == key)).map (·.2)
  | _ => none

def code (value : GatewayWire.Value) : Nat :=
  match field value "exit_code" with
  | some (.integer value) => if 0 ≤ value && value ≤ 255 then value.toNat else 126
  | _ => 126

def errorText (value : GatewayWire.Value) : String :=
  match value with
  | .string message => message
  | _ => match field value "message" with
    | some (.string message) => message
    | _ => "host request failed"

def bundleMetadata (value : GatewayWire.Value) : GatewayWire.Value :=
  match value with
  | .object fields => .object (fields.filterMap (fun (name, value) =>
      if name == "bundle_id" then some (name, value)
      else if name == "manifest_path" then some ("manifest", value) else none))
  | other => other

def cliOutput (parsed : Cli.Parsed) (status : Nat) (value : GatewayWire.Value) :
    Nat × GatewayWire.Value :=
  if status != 0 then
    let diagnostic := GatewayWire.Value.object [("status", .string "rejected"),
      ("entry", .string "no"), ("error", .string (errorText value))]
    match WireJson.render GatewayWire.valueDepthMax diagnostic with
    | .error _ => cliResponse 64 "{\"status\":\"rejected\"}\n".toUTF8
    | .ok bytes => cliResponse 64 (bytes ++ "\n".toUTF8)
  else if parsed.request.command == GatewayWire.validateCommand then
    cliResponse 0 "valid policy\n".toUTF8
  else
    let workload := parsed.request.command == GatewayWire.runCommand ||
      parsed.request.command == GatewayWire.checkCommand
    let metadata := if parsed.request.command == GatewayWire.bundleCommand then bundleMetadata value
      else if workload then (field value "json").getD .null else value
    match WireJson.render GatewayWire.valueDepthMax metadata with
    | .error error => cliResponse 126 .empty (error.toUTF8 ++ "\n".toUTF8)
    | .ok bytes => cliResponse (if workload then code value else 0) (bytes ++ "\n".toUTF8)

-- §FS-host-boundary.caller: CLI and library consume the identical application program.
def cli (request : GatewayWire.Request) : Program (Nat × GatewayWire.Value) := do
  match Cli.parse request with
  | .error error => return cliResponse 2 .empty (Cli.usage ++ error.toUTF8 ++ "\n".toUTF8)
  | .ok .help => return cliResponse 0 Cli.usage
  | .ok (.command parsed) =>
    let (status, value) ← dispatch parsed.request parsed.timeoutNanoseconds
    return cliOutput parsed status value

def run (request : GatewayWire.Request) : Program (Nat × GatewayWire.Value) :=
  if request.command == GatewayWire.cliCommand then cli request else dispatch request

end LeanCage.Host.Commands
