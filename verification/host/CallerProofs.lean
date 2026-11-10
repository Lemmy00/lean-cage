import RequestGuarantee
import RetrievalProofs.Authentication
import EngineIdentityProofs

namespace LeanCage.Host.CallerProofs
open Filesystem
open ApplicationProofs

-- §FS-host-boundary.caller: Bundle and private-key checks come from this same actual caller.
structure AcceptedRun (request : GatewayWire.Request) (duration : Option Nat)
    (events : List Program.Event) (answer : GatewayWire.Value) where
  bundle : Validation.Bundle
  key : ByteArray
  selecting : List (Request × Reply)
  checking : List (Request × Reply)
  engineChecking : List (Request × Reply)
  authenticating : List (Request × Reply)
  executing : List Program.Event
  valid : request.valid = true
  select : Returns (Validation.loadBundle (request.field GatewayWire.bundleSlot).bytes)
    selecting (.ok bundle)
  check : Returns (Validation.checkBundle bundle) checking (.ok ())
  engine : Returns (Validation.checkEngineIdentity bundle) engineChecking (.ok ())
  authenticate : Returns (Publication.authenticationKey bundle) authenticating (.ok key)
  execute : Run (executeRun request bundle duration) executing answer
  trace : events = selecting.map Program.filesystemEvent ++ checking.map Program.filesystemEvent ++
    engineChecking.map Program.filesystemEvent ++ authenticating.map Program.filesystemEvent ++ executing

theorem key_gate_source {events : List (Request × Reply)} (bundle : Validation.Bundle)
    (run : Returns (do
      let key ← Publication.authenticationKey bundle
      pure (key.map (fun _ => ()))) events (.ok ())) :
    ∃ key, Returns (Publication.authenticationKey bundle) events (.ok key) := by
  obtain ⟨first, result, last, copied, final, shape⟩ := Snapshot.returns_bind_split _ _ run
  obtain ⟨rfl, same⟩ := Snapshot.returns_pure_eq final
  cases result with
  | error error => cases same
  | ok key =>
    refine ⟨key, ?_⟩
    rw [shape]
    simpa only [List.append_nil] using copied

-- §FS-host-boundary.acceptance: The public engine supplies the run's bootstrap checks.
theorem accepted_run_source (request : GatewayWire.Request) (duration : Option Nat)
    {events : List Program.Event} {answer : GatewayWire.Value}
    (command : request.command = GatewayWire.runCommand ∨ request.command = GatewayWire.checkCommand)
    (run : Run (executeChecked request duration) events answer) :
    Nonempty (AcceptedRun request duration events answer) := by
  have bundleFalse : (request.command == GatewayWire.bundleCommand) = false := by
    rcases command with command | command <;> rw [command] <;> decide
  have validateFalse : (request.command == GatewayWire.validateCommand) = false := by
    rcases command with command | command <;> rw [command] <;> decide
  have runTrue : (request.command == GatewayWire.runCommand ||
      request.command == GatewayWire.checkCommand) = true := by
    rcases command with command | command <;> rw [command] <;> decide
  unfold executeChecked at run
  simp only [bundleFalse, validateFalse, runTrue, Bool.false_eq_true, ↓reduceIte] at run
  obtain ⟨guarding, guarded, afterGuard, guard, run, guardShape⟩ := bind_source _ _ run
  cases guarded
  obtain ⟨valid, _, rfl⟩ := check_request_source request guard
  obtain ⟨selecting, bundle, later, selected, run, selectShape⟩ := bind_source _ _ run
  obtain ⟨checking, checked, later, checkedRun, run, checkShape⟩ := bind_source _ _ run
  cases checked
  obtain ⟨engineChecking, engineChecked, later, engineRun, run, engineShape⟩ := bind_source _ _ run
  cases engineChecked
  obtain ⟨authenticating, authenticated, executing, keyRun, run, keyShape⟩ := bind_source _ _ run
  cases authenticated
  obtain ⟨selectSource, selected, selectEvents⟩ := filesystem_source _ selected
  obtain ⟨checkSource, checkedRun, checkEvents⟩ := filesystem_source _ checkedRun
  obtain ⟨engineSource, engineRun, engineEvents⟩ := filesystem_source _ engineRun
  obtain ⟨keySource, keyRun, keyEvents⟩ := filesystem_source _ keyRun
  obtain ⟨key, keyRun⟩ := key_gate_source bundle keyRun
  refine ⟨⟨bundle, key, selectSource, checkSource, engineSource, keySource, executing,
    valid, selected, checkedRun, engineRun, keyRun, run, ?_⟩⟩
  simp only [guardShape, selectShape, checkShape, engineShape, keyShape, selectEvents, checkEvents, engineEvents,
    keyEvents, List.nil_append, List.append_assoc]
-- §FS-host-boundary.acceptance: Native/CLI callers consume this complete engine-source result.
theorem actual_application_complete (request : GatewayWire.Request) (duration : Option Nat)
    {events : List Program.Event} {answer : GatewayWire.Value}
    (command : request.command = GatewayWire.runCommand ∨ request.command = GatewayWire.checkCommand)
    (run : Program.Returns (execute request duration) events (.ok answer))
    (complete : RequestGuarantee.statusField answer = some "complete") :
    ∃ accepted : AcceptedRun request duration events answer,
      Nonempty (RequestGuarantee.CompleteRun request accepted.bundle duration accepted.executing answer) := by
  obtain ⟨accepted⟩ := accepted_run_source request duration command run
  exact ⟨accepted, RequestGuarantee.execute_complete request accepted.bundle duration accepted.execute complete⟩

end LeanCage.Host.CallerProofs
