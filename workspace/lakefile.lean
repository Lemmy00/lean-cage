import Lake
open Lake DSL

-- §AR-workspace.interfaces: Extend M2 in an isolated package with preserved dependency pins.
package leanCageM3 where
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`warningAsError, true⟩]

require leanCageM2 from "../m2"

@[default_target]
lean_lib LeanCageM3

-- §AR-metadata.primitives: Share the narrow metadata adapter across public and entry callers.
extern_lib metadataPrimitives pkg := do
  let source ← inputFile (pkg.dir / ".." / "linux" / "metadata_primitives.c") true
  let object ← buildO (pkg.buildDir / "native" / "metadata_primitives.o") source
    #["-I", (← getLeanIncludeDir).toString]
    #["-std=c11", "-O2", "-Wall", "-Wextra", "-Werror", "-fPIC"]
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "metadata_primitives") #[object]

lean_exe «leancage» where
  root := `Main
