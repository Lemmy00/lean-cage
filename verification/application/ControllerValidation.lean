import WorkspaceController
import LeanCageHost.Validation

namespace LeanCage.Application.ControllerValidation
open Lean LeanCageM3

-- §AR-host-boundary.coverage: The host invokes this exact branch of the maintained controller.
def validationOnly (path : String) : IO UInt32 := do
  try
    match decodePolicy (← readBounded path 65536) with
    | .ok _ => IO.println "valid policy"; return 0
    | .error error => IO.println error; return 64
  catch error =>
    IO.println (Lean.Json.mkObj [("termination", "unknown"), ("entry", "unknown"),
      ("cleanup", "unknown"), ("error", toJson error.toString)]).compress
    return 126

-- §AR-application-verification.host: Checked equality rules out the helper-launch branch here.
theorem actual_validator_command (path : String) :
    _root_.main ["validate-policy", path] = validationOnly path := by
  rfl

-- §FS-host-boundary.caller: Caller data is a file argument after a fixed command selector.
theorem host_validator_arguments (bundle : LeanCage.Host.Validation.Bundle) (path : String) :
    (LeanCage.Host.Validation.validatorArguments bundle path).cmd = bundle.root ++ "/bin/controller" ∧
    (LeanCage.Host.Validation.validatorArguments bundle path).args = #["validate-policy", path] ∧
    (LeanCage.Host.Validation.validatorArguments bundle path).inheritEnv = false := by
  exact ⟨rfl, rfl, rfl⟩

end LeanCage.Application.ControllerValidation
