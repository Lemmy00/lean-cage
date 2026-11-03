import Lake
open Lake DSL

-- §FS-linux-product.proofs: Public aliases consume the same checked executable definitions.
package leanCageWorkspace where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`warningAsError, true⟩]

require leanCageM3 from "../workspace"

@[default_target]
lean_lib LeanCageWorkspace
