import FilesystemCustodyPrefix
import FilesystemNativeHandoff

namespace LeanCage.Host.Kernel
open Filesystem

private theorem launch_shared {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {before after : Population} {actor : ActorId}
    {references : UInt64 → Option Handle} {closeExec : UInt64 → Bool} {workingDirectory : ObjectId}
    (actual : ActorStep runtime (.launch actor references closeExec workingDirectory) before after) :
    after.shared = before.shared := by cases actual; rfl

-- §FS-host-boundary.caller: A launch uses the actual exec table's 0/1/3 channel projection.
-- Complementary SDK references stay in the native handoff rather than becoming raw engine FDs.
theorem launched_engine_references_owned {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {ticks : List (ActorTick runtime)}
    {before after : Population} {actor : ActorId} {references : UInt64 → Option Handle}
    {closeExec : UInt64 → Bool} {workingDirectory : ObjectId} {family : Family}
    {initialObjects : ObjectId → Bool} {dataObjects ipc : ObjectId → Prop}
    {catalogue : Catalogue runtime ticks}
    (actual : ActorStep runtime (.launch actor references closeExec workingDirectory) before after)
    (binding : InitialEngineBinding ipc references closeExec)
    (separate : ∀ object, ipc object → ¬ dataObjects object)
    (graph : FamilyGraph before.shared family initialObjects dataObjects)
    (owned : EngineReferencesOwned runtime ticks before family catalogue) :
    EngineReferencesOwned runtime ticks after family catalogue := by
  cases actual with
  | @launch population actor references closeExec workingDirectory fresh absent inherited =>
    intro query engine present fd handle scope live privateObject
    by_cases same : query = actor
    · subst query
      simp only [Population.launch, Population.install, ite_eq_left] at present
      have engineSame := Option.some.inj present
      subst engine
      have denied := initial_reference_outside_data binding separate live
      exact False.elim (denied (graph.data handle.object scope privateObject))
    · exact owned query engine (by
        simpa only [Population.launch, Population.install, ite_eq_right same] using present)
        fd handle scope live privateObject

-- §FS-host-boundary.ownership: The handoff extends the same already-derived custody prefix.
-- Its binding is on the SAME recorded execution snapshot, not an independent initial table.
theorem native_handoff_custody_prefix {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} (descriptors : DescriptorContract kernel)
    (lifetimes : LifetimeContract runtime) (references : ReferenceContract runtime)
    {initial : World} {ticks processed : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories ipc : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignReferences : ForeignReferences} {tick : ActorTick runtime} {nativeBefore : NativeProcesses}
    (handoff : NativeHandoffAt tick nativeBefore)
    (binding : InitialEngineBinding ipc handoff.execution.references.rawProjection.handles
      handoff.execution.references.rawProjection.closeOnExec)
    (separate : ∀ object, ipc object → ¬ dataObjects object)
    (prior : CustodyPrefix runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences processed tick.before) :
    Nonempty (CustodyPrefix runtime initial ticks hostUid dataObjects directories semantics
      foreignReferences (processed ++ [tick]) tick.after) := by
  have actual : ActorStep runtime (.launch handoff.actor handoff.execution.references.rawProjection.handles
      handoff.execution.references.rawProjection.closeOnExec handoff.execution.references.workingDirectory)
      tick.before tick.after := handoff.action ▸ tick.operation
  have shared : tick.after.shared = tick.before.shared := launch_shared actual
  have owned := launched_engine_references_owned actual binding separate prior.namespaceState.graph prior.references
  have state : NamespaceCustody tick.after.shared prior.caps hostUid initial.allocated dataObjects
      directories foreignReferences := shared ▸ prior.namespaceState
  exact ⟨prior.advance descriptors lifetimes references prior.caps prior.catalogue state
    (shared ▸ prior.names) prior.coverage (shared ▸ prior.valid) owned .same⟩

end LeanCage.Host.Kernel
