import FilesystemExecutableCustody

namespace LeanCage.Host.Kernel
open Filesystem

-- §AR-host-boundary.primitives: Operator installation identifies the protected
-- native engine path/image independently of a public --bundle selection.
structure InstalledEngine {initial : World} (catalogue : BootstrapCatalogue initial) where
  root : String
  authorized : catalogue.roots root
  path : ByteArray
  image : ObjectId
  identified : catalogue.files root "bin/leancage-host" image

-- §AR-host-boundary.primitives: ONE actual exec resolves the protected installed
-- pathname. It promises no spawn, exec, SDK return, or source argument success.
structure InstalledEngineLookup {kernel : Contract} (native : NativePrimitive kernel)
    {initial : World} {catalogue : BootstrapCatalogue initial} (installed : InstalledEngine catalogue) : Prop where
  resolved : ∀ token caller processes next before after arguments observed image,
    native.observed token caller processes before (.exec arguments) observed (.executed image) next after →
    arguments.path = installed.path → image = installed.image

-- §FS-host-boundary.caller: The SAME journal's actual exec and source-selected
-- path establish the handoff image. A future SDK success is not an input.
def NativeLaunchOrigin.installed_selection {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat}
    {before after : Processes} {initial current : NativeProcesses} {ticks : List (ActorTick runtime)}
    {tick : ActorTick runtime} {handoff : NativeHandoffAt tick current}
    (origin : NativeLaunchOrigin process child native hostUid before after initial current ticks handoff)
    {first : World} {catalogue : BootstrapCatalogue first}
    (installed : InstalledEngine catalogue) (lookup : InstalledEngineLookup native installed)
    (path : handoff.execution.arguments.path = installed.path) :
    BootstrapExecutableSelection catalogue (current.transfer handoff.actor handoff.execution) handoff.actor := by
  obtain ⟨operation, _⟩ := native_execution_actual_table origin.execution
  have actual := origin.execution.call.native
  rw [operation, origin.execution.product] at actual
  have image := lookup.resolved _ _ _ _ _ _ _ _ _ actual path
  exact {
    handoff := ⟨handoff.actor, handoff.execution⟩
    current := (native_transfer_consumed current handoff.actor handoff.execution).2.2
    token := rfl
    root := installed.root
    authorized := installed.authorized
    identified := image ▸ installed.identified }

end LeanCage.Host.Kernel
