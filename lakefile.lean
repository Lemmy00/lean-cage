import Lake
open Lake DSL

-- §AR-m1-launch.binding: Track native source changes in the executable's build dependencies.
package leanCage where
  version := v!"0.0.0"
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`warningAsError, true⟩]

require velvet from git "https://github.com/verse-lab/velvet" @
  "836ed5a163b36c09081ed1d8aeecd3cec040f87e"

@[default_target]
lean_lib LeanCage

extern_lib leanCageNative pkg := do
  let source ← inputFile (pkg.dir / "native" / "leancage_m1.c") true
  let object ← buildO (pkg.buildDir / "native" / "leancage_m1.o") source
    #["-I", (← getLeanIncludeDir).toString]
    #["-std=c11", "-O2", "-Wall", "-Wextra", "-Werror", "-fPIC"]
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "leancage_m1") #[object]

lean_exe «leancage-m1» where
  root := `M1Main
  moreLinkArgs := #["-Wl,-z,now"]
