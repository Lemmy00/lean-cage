import Lake
open Lake DSL

-- §AR-entry.effects: The entry image has its own bounded runtime/adapter surface.
package leanCageEntry where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`warningAsError, true⟩]

require leanCageM3 from "../workspace"

@[default_target]
lean_lib LeanCageEntry

lean_lib EntryVerification where
  srcDir := "../verification/launch"
  roots := #[`Admission, `StateProofs, `Witnesses, `Effects, `WorkerConnection]

extern_lib entryPrimitives pkg := do
  let source ← inputFile (pkg.dir / ".." / "linux" / "entry_primitives.c") true
  let object ← buildO (pkg.buildDir / "native" / "entry_primitives.o") source
    #["-I", (← getLeanIncludeDir).toString]
    #["-std=c11", "-O2", "-Wall", "-Wextra", "-Werror", "-fPIC"]
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "entry_primitives") #[object]

lean_exe «leancage-entry» where
  root := `Main
  moreLinkArgs := #["-Wl,-z,now", "-Wl,--wrap=initialize_libuv",
    "-Wl,--wrap=lean_init_task_manager", "-Wl,--wrap=lean_run_main",
    "-Wl,--wrap=pthread_create"]

lean_exe «leancage-entry-test» where
  root := `TestMain
  moreLinkArgs := #["-Wl,-z,now", "-Wl,--wrap=initialize_libuv",
    "-Wl,--wrap=lean_init_task_manager", "-Wl,--wrap=lean_run_main",
    "-Wl,--wrap=pthread_create"]
