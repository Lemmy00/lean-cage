import Lake
open Lake DSL

-- §AR-application-verification.method: Compose packages without a runtime cycle.
package leanCageApplicationVerification where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`warningAsError, true⟩]

require leanCageM3 from "../../workspace"
require leanCageHost from "../../host"

@[default_target]
lean_lib ApplicationVerification where
  roots := #[`ControllerValidation, `ControllerFilesystem, `ControllerChildEffects, `WorkspaceController]
