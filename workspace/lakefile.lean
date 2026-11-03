import Lake
open Lake DSL

-- §AR-workspace.interfaces: Extend M2 in an isolated package with preserved dependency pins.
package leanCageM3 where
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`warningAsError, true⟩]

require leanCageM2 from "../m2"

@[default_target]
lean_lib LeanCageM3

lean_exe «leancage» where
  root := `Main
