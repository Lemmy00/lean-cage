import LeanCageHost.Image
import LeanCageHost.RunDirectory
import LeanCageHost.VirtualMachine
import LeanCageHost.Publication
import LeanCageHost.Retrieval

namespace LeanCage.Host
open Filesystem

abbrev Checked (α : Type) := ExceptT Failure Program α

def filesystem {α : Type} (program : Filesystem.Program (Filesystem.Result α)) : Checked α :=
  ExceptT.mk (Program.liftFilesystem program)

def checked {α : Type} (value : Except String α) : Checked α :=
  ExceptT.mk (pure (value.mapError (fun (error : String) => (error : Failure))))

def effectful {α : Type} (program : Program (Filesystem.Result α)) : Checked α :=
  ExceptT.mk program

def inputWorkspace (request : GatewayWire.Request) : Option ByteArray :=
  let field := request.field GatewayWire.workspaceSlot
  if field.kind == GatewayWire.pathKind then some field.bytes else none

def inputStdin (request : GatewayWire.Request) : Snapshot.Stdin :=
  let field := request.field GatewayWire.stdinSlot
  if field.kind == GatewayWire.rawKind then .bytes field.bytes
  else if field.kind == GatewayWire.pathKind then .file field.bytes else .absent

-- §FS-host-boundary.snapshot: Validation, copying, binding and second validation share exact bytes.
def preparePolicy (request : GatewayWire.Request) (bundle : Validation.Bundle) :
    Checked (Policy.Accepted × Snapshot.Frozen) := do
  let raw ← filesystem (Validation.loadPolicy request)
  let value ← effectful (Validation.validateCopied bundle raw)
  let accepted ← checked (Policy.budgets value raw)
  let frozen ← filesystem (Snapshot.freeze (inputWorkspace request) (inputStdin request) accepted.snapshot)
  let bound ← checked (Policy.bind accepted frozen)
  let validated ← effectful (Validation.validateCopied bundle bound.raw)
  if Validation.stringField validated "profile" != Validation.stringField bundle.manifest "profile" ||
      Validation.stringField validated "runtime_manifest_digest" !=
        Validation.stringField bundle.manifest "runtime_manifest_digest" then
    throw ("policy and selected bundle profile differ" : Failure)
  let final ← checked (Policy.budgets validated bound.raw)
  if !final.sameBudgets accepted then
    throw ("bound policy changed the copied-input or transport budgets" : Failure)
  return (final, frozen)

def expected (bundle : Validation.Bundle) (preflight : Bool) (limits : Transport.Limits) :
    Except String Artifacts.Expected := do
  let some profile := Validation.stringField bundle.manifest "profile"
    | throw "bundle profile is absent"
  let some runtime := Validation.stringField bundle.manifest "runtime_manifest_digest"
    | throw "bundle runtime identity is absent"
  return ⟨preflight, profile, runtime, limits⟩

def incomplete (request bundle : String) (preflight : Bool) (cleanup : String)
    (report : Option Json.Value) (error : Option String) : Outcome := {
  requestId := request
  bundleId := bundle
  command := if preflight then "check" else "run"
  status := "incomplete"
  report
  exitCode := 126
  vmCleanup := cleanup
  error }

-- §FS-host-boundary.artifacts: Errors preserve reports and withhold complete artifacts.
def receive (request : String) (bundle : Validation.Bundle) (preflight : Bool)
    (policy : Policy.Accepted) (vm : VirtualMachine.Result) :
    Filesystem.Program Publication.Input := do
  let raw := vm.transport.report?
  let known := raw.bind (Artifacts.knownReport preflight)
  let outcome := incomplete request bundle.identity preflight vm.cleanup known vm.error
  let base : Publication.Input := ⟨outcome, policy, vm.boot, raw, none, none⟩
  if vm.error.isSome then return base
  match vm.transport.finish with
  | .error error => return { base with outcome := { outcome with error := some error } }
  | .ok transport =>
    match expected bundle preflight policy.transport with
    | .error error => return { base with outcome := { outcome with error := some error } }
    | .ok expected =>
      let validated ← Artifacts.validate expected transport
      match validated with
      | .error error => return { base with outcome := { outcome with error := some error.message } }
      | .ok validated => return {
        base with
        received := some transport
        validated := some validated
        outcome := { outcome with
          status := "complete"
          report := some validated.report
          exitCode := transport.terminal.controller
          stdout := validated.stdout
          stderr := validated.stderr
          files := validated.files } }

-- §FS-host-boundary.snapshot: Image failure prevents the actual VM call and keeps its error.
def dispatchImage (request : String) (bundle : Validation.Bundle) (preflight : Bool)
    (policy : Policy.Accepted) (run : RunDirectory.Owned) (duration : Nat)
    (transport : Transport.State) (image : Filesystem.Result Unit) : Program Publication.Input :=
  match image with
  | .error error => pure {
    outcome := incomplete request bundle.identity preflight "not_started" none (some error.message)
    policy
    boot := ByteArray.empty
    rawReport := none
    received := none
    validated := none }
  | .ok _ => do
    let vm ← VirtualMachine.run bundle run.path duration transport
    Program.liftFilesystem (receive request bundle preflight policy vm)

-- §FS-host-boundary.ownership: Unknown VM reaping retains files instead of deleting live backing.
def cleanupRun (run : RunDirectory.Owned) (input : Publication.Input) : Program Unit :=
  if input.outcome.vmCleanup == "unknown" then do
    let _ ← Program.liftFilesystem <|
      Filesystem.Program.effect { op := .close, first := run.directory.fd }
    let _ ← Program.liftFilesystem <|
      Filesystem.Program.effect { op := .close, first := run.container.fd }
    pure ()
  else Program.liftFilesystem (RunDirectory.cleanup run)

def requestDuration (request : GatewayWire.Request) (policy : Policy.Accepted)
    (override : Option Nat) : Checked Nat :=
  match override with
  | none => checked (Policy.timeoutNanoseconds (request.field GatewayWire.timeoutSlot) policy.wallMilliseconds)
  | some duration =>
    if duration == 0 || duration > 3660000000000 then
      throw ("VM timeout is outside the supported bound" : Failure)
    else pure duration

def executeRun (request : GatewayWire.Request) (bundle : Validation.Bundle)
    (durationOverride : Option Nat) : Checked GatewayWire.Value := do
  let (policy, frozen) ← preparePolicy request bundle
  let random ← filesystem (Directories.randomBytes 17 16 .empty)
  let identity := Snapshot.hex random
  let preflight := request.command == GatewayWire.checkCommand
  let duration ← requestDuration request policy durationOverride
  let transport ← checked (Transport.State.init identity.toUTF8 bundle.identity.toUTF8 policy.transport)
  let run ← filesystem RunDirectory.create
  let image : Filesystem.Result Unit ← ExceptT.lift <| Program.liftFilesystem <|
    Image.create run.directory.fd bundle (Image.entries identity bundle.identity preflight request.fault policy frozen)
  let input ← ExceptT.lift (dispatchImage identity bundle preflight policy run duration transport image)
  let _ ← ExceptT.lift (cleanupRun run input)
  let published ← ExceptT.lift (Program.liftFilesystem (Publication.publish request bundle input))
  return published.outcome.wire published.metadata

def checkRequest (request : GatewayWire.Request) : Checked Unit :=
  if !request.valid || request.command == GatewayWire.cliCommand then
    throw ("invalid application request" : Failure)
  else pure ()

-- §FS-host-boundary.acceptance: The public callers execute this same effect program.
def executeChecked (request : GatewayWire.Request) (durationOverride : Option Nat := none) :
    Checked GatewayWire.Value := do
  let _ ← checkRequest request
  let bundle ← filesystem (Validation.loadBundle (request.field GatewayWire.bundleSlot).bytes)
  let _ ← filesystem (Validation.checkBundle bundle)
  let _ ← filesystem (Validation.checkEngineIdentity bundle)
  let _ ← filesystem (do
    let key ← Publication.authenticationKey bundle
    return key.map (fun _ => ()))
  if request.command == GatewayWire.bundleCommand then
    return .object [("bundle_id", .string bundle.identity),
      ("manifest", Validation.jsonToWire bundle.manifest),
      ("manifest_path", .path (bundle.root ++ "/manifest.json").toUTF8)]
  else if request.command == GatewayWire.validateCommand then
    let raw ← filesystem (Validation.loadPolicy request)
    let value ← effectful (Validation.validateCopied bundle raw)
    return Validation.jsonToWire value
  else if request.command == GatewayWire.runCommand || request.command == GatewayWire.checkCommand then
    executeRun request bundle durationOverride
  else if request.command == GatewayWire.reportCommand then
    filesystem (Retrieval.report request bundle)
  else throw ("unsupported host command" : Failure)

def execute (request : GatewayWire.Request) (durationOverride : Option Nat := none) :
    Program (Filesystem.Result GatewayWire.Value) :=
  (executeChecked request durationOverride).run

end LeanCage.Host
