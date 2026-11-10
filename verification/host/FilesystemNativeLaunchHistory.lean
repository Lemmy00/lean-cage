import FilesystemNativeExecutions
import FilesystemNativeForkRows
import FilesystemNativeExecRows
import FilesystemCustodyState
import FilesystemRegisteredCustody

namespace LeanCage.Host.Kernel
open Filesystem

variable {sourceProgram : Program UInt32}

-- §FS-host-boundary.caller: Both cuts are selected from the actual prefix preceding this
-- handoff. The birth's local prefix index is its SAME complete-history position.
structure NativeLaunchOrigin {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (process : ProcessContract runtime) (child : ChildPrimitive kernel)
    (native : NativePrimitive kernel) (hostUid : Nat)
    (before after : Processes) (initial current : NativeProcesses) (ticks : List (ActorTick runtime))
    {tick : ActorTick runtime} (handoff : NativeHandoffAt tick current) where
  execution : NativeExecutionCut process child native hostUid before after initial current ticks
    handoff.actor handoff.execution
  birth : NativeBirthCut process child native hostUid before execution.priorProcesses
    initial execution.priorNative execution.leading handoff.actor
  earlier : birth.position < execution.position
  selected : ticks[birth.position]? = some birth.tick

-- §FS-host-boundary.ownership: A child cannot use an initial/future birth, independent
-- exec fixture, or successful SDK acknowledgement in place of its own recorded origin.
theorem native_launch_origin {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat}
    {before after : Processes} {initial current : NativeProcesses} {ticks : List (ActorTick runtime)}
    (journal : NativeExternalJournal process child native hostUid before initial ticks after current)
    {tick : ActorTick runtime} (handoff : NativeHandoffAt tick current)
    (unborn : initial.allocated handoff.actor = false) (noImage : initial.executions handoff.actor = none) :
    Nonempty (NativeLaunchOrigin process child native hostUid before after initial current ticks handoff) := by
  obtain ⟨execution⟩ := native_handoff_execution journal handoff noImage
  obtain ⟨birth, earlier, selected⟩ := native_execution_birth_before execution unborn
  exact ⟨⟨execution, birth, earlier, selected⟩⟩

namespace NativeLaunchOrigin

variable {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel}
  {native : NativePrimitive kernel} {hostUid : Nat}
  {before after : Processes} {initial current : NativeProcesses} {ticks : List (ActorTick runtime)}
  {tick : ActorTick runtime} {handoff : NativeHandoffAt tick current}

-- §AR-host-boundary.interfaces.gateway: The C producer interprets THIS extracted birth
-- call, not another call on the same foreign tick. Entry and header facts remain source-produced.
def bindBirth (origin : NativeLaunchOrigin process child native hostUid before after initial current ticks handoff)
    {key : NativeCode.SourceKey} {code : NativeCode.CallRow}
    (interpreted : NativeCode.Interprets code origin.birth.call)
    (parent : code.process = key.process) (entry : key.entryPosition ≤ origin.birth.position)
    (headers : key.actionsLifetime ≠ key.attributesLifetime) :
    NativeCode.SelectedCall native ticks key origin.birth.priorNative origin.birth.nextNative code :=
  NativeCode.bindSourceRow ⟨origin.birth.tick, origin.selected, origin.birth.call, interpreted⟩ parent entry headers

def execRow (origin : NativeLaunchOrigin process child native hostUid before after initial current ticks handoff)
    {code : NativeCode.CallRow} (interpreted : NativeCode.Interprets code origin.execution.call) :
    NativeCode.PrimitiveRowAt native ticks origin.execution.position
      origin.execution.priorNative origin.execution.nextNative code :=
  ⟨origin.execution.tick, origin.execution.selected, origin.execution.call, interpreted⟩

-- §FS-host-boundary.ownership: The source-built spawn, its parent and child lifetime,
-- and the currently retained birth all come from one actual creation row.
theorem birth_source (origin : NativeLaunchOrigin process child native hostUid before after initial current ticks handoff)
    {key : NativeCode.SourceKey} {code : NativeCode.CallRow} {arguments : NativeCode.Spawn}
    (interpreted : NativeCode.Interprets code origin.birth.call)
    (parent : code.process = key.process) (operation : code.operation = .spawn arguments) :
    origin.birth.birth.parent = key.process ∧ NativeCode.encodeSpawn origin.birth.arguments = arguments ∧
      code.product = .created handoff.actor ∧ current.births handoff.actor = some origin.birth.birth := by
  have encoded := NativeCode.operation_exact interpreted.operation
  rw [origin.birth.operation, operation] at encoded
  have encodedArguments : NativeCode.encodeSpawn origin.birth.arguments = arguments := by
    simpa only [NativeCode.encodeOperation, NativeCode.Operation.spawn.injEq] using encoded
  have committed := NativeCode.product_exact interpreted.product
  rw [origin.birth.product] at committed
  have beforeExec := native_birth_retained origin.birth
  have afterExec := native.birth_frame _ _ _ _ _ _ _ _ _ _ _ origin.execution.call.native beforeExec
  exact ⟨origin.birth.parent.trans (interpreted.process.symm.trans parent), encodedArguments,
    by simpa only [NativeCode.encodeProduct] using committed.symm,
    native_journal_birth_frame origin.execution.last afterExec⟩

-- §FS-host-boundary.ownership: Only source-held slots are constrained separately. Every
-- other inherited FD and CWD stays this actual full fork snapshot's value.
theorem fork_references (origin : NativeLaunchOrigin process child native hostUid before after initial current ticks handoff)
    (fork : NativeCode.ForkReferences (runtime := runtime) native) :
    origin.birth.nextNative.references handoff.actor = some origin.birth.call.beforeReferences :=
  fork.cloned origin.birth.tick origin.birth.priorNative origin.birth.nextNative origin.birth.call
    handoff.actor origin.birth.product

-- §FS-host-boundary.caller: Channels are taken from the SAME extracted exec's actual
-- output table, then the handoff's still-current snapshot. Spawn success is not exec evidence.
theorem initial_binding (origin : NativeLaunchOrigin process child native hostUid before after initial current ticks handoff)
    {code : NativeCode.CallRow} (interpreted : NativeCode.Interprets code origin.execution.call)
    {data control : Nat} (evidence : NativeChannels.Evidence code.afterReferences data control)
    (ipc : Nat → Prop) (dataIpc : ipc data) (controlIpc : ipc control) :
    origin.execution.call.operation = .exec handoff.execution.arguments ∧
      origin.execution.call.afterReferences = handoff.execution.references ∧
      current.references handoff.actor = some handoff.execution.references ∧
      Nonempty (InitialEngineBinding ipc handoff.execution.references.rawProjection.handles
        handoff.execution.references.rawProjection.closeOnExec) := by
  obtain ⟨operation, table⟩ := native_execution_actual_table origin.execution
  have actualEvidence : NativeChannels.Evidence
      (NativeCode.encodeReferences handoff.execution.references) data control := by
    simpa only [interpreted.output, table] using evidence
  exact ⟨operation, table, handoff.current,
    ⟨NativeChannels.initial_binding_of_native_evidence handoff.execution.references data control actualEvidence
      ipc dataIpc controlIpc⟩⟩

-- §FS-host-boundary.caller: The source-bound channel snapshot feeds the actual common
-- custody consumer directly; no independently supplied initial channel/owner role remains.
theorem owned_handoff (origin : NativeLaunchOrigin process child native hostUid before after initial current ticks handoff)
    {code : NativeCode.CallRow} (interpreted : NativeCode.Interprets code origin.execution.call)
    {data control : Nat} (evidence : NativeChannels.Evidence code.afterReferences data control)
    (ipc : Nat → Prop) (dataIpc : ipc data) (controlIpc : ipc control)
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime)
    {first : World} {trailing : List (ActorTick runtime)}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignReferences : ForeignReferences}
    (separate : ∀ object, ipc object → ¬ dataObjects object)
    (prior : CustodyState runtime first (ticks ++ tick :: trailing) hostUid dataObjects directories semantics
      foreignReferences ticks tick.before current) :
    Nonempty (CustodyState runtime first (ticks ++ tick :: trailing) hostUid dataObjects directories semantics
      foreignReferences (ticks ++ [tick]) tick.after (current.transfer handoff.actor handoff.execution)) := by
  obtain ⟨operation, table, actualCurrent, binding⟩ := origin.initial_binding interpreted evidence ipc dataIpc controlIpc
  obtain ⟨binding⟩ := binding
  exact handoff_custody_state descriptors lifetimes references handoff binding separate prior

end NativeLaunchOrigin

-- §FS-host-boundary.caller: The same extracted source-bound exec advances the registered
-- global custody history, preserving the catalogue and consuming the current native token.
theorem native_registered_handoff {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat}
    {before after : Processes} {initial current : NativeProcesses} {ticks : List (ActorTick runtime)}
    {tick : ActorTick runtime} {handoff : NativeHandoffAt tick current}
    (origin : NativeLaunchOrigin process child native hostUid before after initial current ticks handoff)
    {code : NativeCode.CallRow} (interpreted : NativeCode.Interprets code origin.execution.call)
    {data control : Nat} (evidence : NativeChannels.Evidence code.afterReferences data control)
    (ipc : Nat → Prop) (dataIpc : ipc data) (controlIpc : ipc control)
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime)
    {first : World} {trailing : List (ActorTick runtime)}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {foreignReferences : ForeignReferences}
    (separate : ∀ object, ipc object → ¬ dataObjects object)
    (prior : RegisteredCustodyState runtime first (ticks ++ tick :: trailing) hostUid dataObjects directories semantics
      foreignReferences ticks tick.before current) :
    Nonempty (RegisteredCustodyState runtime first (ticks ++ tick :: trailing) hostUid dataObjects directories semantics
      foreignReferences (ticks ++ [tick]) tick.after (current.transfer handoff.actor handoff.execution)) := by
  obtain ⟨operation, table, actualCurrent, ⟨binding⟩⟩ := origin.initial_binding interpreted evidence ipc dataIpc controlIpc
  obtain ⟨next, catalogue⟩ := handoff_custody_state_catalogued descriptors lifetimes references
    handoff binding separate prior.current
  have noRoot : ¬ Nonempty (PrimitiveRootUse runtime first (ticks ++ tick :: trailing) tick) :=
    no_root_use_of_nonfilesystem (by rw [handoff.action]; intro invalid; cases invalid)
  exact ⟨prior.other next noRoot catalogue⟩

end LeanCage.Host.Kernel
