import Lake
open Lake DSL

-- §AR-lifecycle.design: Depend on the preserved M1 package without changing its pins.
package leanCageM2 where
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`warningAsError, true⟩]

require leanCage from ".."

@[default_target]
lean_lib LeanCageM2

lean_exe «leancage-m2» where
  root := `Main
