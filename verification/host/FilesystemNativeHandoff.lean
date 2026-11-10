import FilesystemNativeBirths
import FilesystemInitial

namespace LeanCage.Host.Kernel
open Filesystem

variable {sourceProgram : Program UInt32}

theorem native_transfer_parent {processes : NativeProcesses} {actor parent : ActorId}
    {execution : NativeExecution} (different : parent ≠ actor) :
    (processes.transfer actor execution).references parent = processes.references parent ∧
      (processes.transfer actor execution).nativeOwned parent = processes.nativeOwned parent := by
  simp only [NativeProcesses.transfer, ite_eq_right different, and_self]

-- §FS-host-boundary.caller: The old native role cannot later act using an obsolete engine table.
theorem native_transfer_consumed (processes : NativeProcesses) (actor : ActorId) (execution : NativeExecution) :
    (processes.transfer actor execution).references actor = none ∧
      (processes.transfer actor execution).nativeOwned actor = false ∧
      (processes.transfer actor execution).handoffs actor = some ⟨actor, execution⟩ := by
  simp only [NativeProcesses.transfer, ite_eq_left, and_self]

theorem native_transfer_retains_support (processes : NativeProcesses) (actor : ActorId)
    (execution : NativeExecution) :
    ∃ handoff, (processes.transfer actor execution).handoffs actor = some handoff ∧
      handoff.execution.references = execution.references ∧
      ∀ fd, (handoff.execution.references.rawProjection.handles fd).orElse
        (fun _ => handoff.execution.references.supportProjection.handles fd) = execution.references.handles fd :=
  ⟨⟨actor, execution⟩, (native_transfer_consumed processes actor execution).2.2, rfl,
    native_reference_partition execution.references⟩

-- §AR-host-boundary.primitives: Only the explicit raw 0/1/3 projection has an absence theorem.
theorem native_raw_other_absent (references : NativeReferences) (fd : UInt64)
    (zero : fd ≠ 0) (one : fd ≠ 1) (three : fd ≠ 3) : references.rawProjection.handles fd = none := by
  simp only [NativeReferences.rawProjection, NativeReferences.engineSlot, beq_eq_false_iff_ne.mpr zero,
    beq_eq_false_iff_ne.mpr one, beq_eq_false_iff_ne.mpr three, Bool.or_self, Bool.false_eq_true, ↓reduceIte]

theorem native_support_other_retained (references : NativeReferences) (fd : UInt64)
    (zero : fd ≠ 0) (one : fd ≠ 1) (three : fd ≠ 3) :
    references.supportProjection.handles fd = references.handles fd := by
  simp only [NativeReferences.supportProjection, NativeReferences.engineSlot, beq_eq_false_iff_ne.mpr zero,
    beq_eq_false_iff_ne.mpr one, beq_eq_false_iff_ne.mpr three, Bool.or_self, Bool.false_eq_true, ↓reduceIte]

-- §FS-host-boundary.caller: The same actual exec table supplies all raw inherited channels;
-- stderr and SDK references remain in its complementary support view.
theorem native_projected_channels (references : NativeReferences) (dataEndpoint cancellationEndpoint : ObjectId)
    (input : rawObjects references.handles 0 = some dataEndpoint)
    (output : rawObjects references.handles 1 = some dataEndpoint)
    (cancel : rawObjects references.handles 3 = some cancellationEndpoint)
    (separate : dataEndpoint ≠ cancellationEndpoint)
    (inputInherited : references.closeOnExec 0 = false)
    (outputInherited : references.closeOnExec 1 = false)
    (cancelInherited : references.closeOnExec 3 = false) :
    EngineChannels (rawObjects references.rawProjection.handles) (rawCloseExec references.rawProjection.closeOnExec)
      dataEndpoint cancellationEndpoint := by
  constructor
  · exact input
  · exact output
  · exact cancel
  · exact separate
  · intro fd zero one three
    by_cases bounded : fd < 2 ^ 64
    · have machineZero : UInt64.ofNat fd ≠ 0 := by
        intro same
        have value := congrArg UInt64.toNat same
        simp only [UInt64.toNat_ofNat_of_lt' bounded] at value
        exact zero value
      have machineOne : UInt64.ofNat fd ≠ 1 := by
        intro same
        have value := congrArg UInt64.toNat same
        simp only [UInt64.toNat_ofNat_of_lt' bounded] at value
        exact one value
      have machineThree : UInt64.ofNat fd ≠ 3 := by
        intro same
        have value := congrArg UInt64.toNat same
        simp only [UInt64.toNat_ofNat_of_lt' bounded] at value
        exact three value
      simp only [rawObjects, bounded, ↓reduceIte,
        native_raw_other_absent references _ machineZero machineOne machineThree, Option.map_none]
    · simp only [rawObjects, bounded, ↓reduceIte]
  · exact inputInherited
  · exact outputInherited
  · exact cancelInherited

private theorem launch_actor_present {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {before after : Population} {actor : ActorId} {references : UInt64 → Option Handle}
    {closeExec : UInt64 → Bool} {workingDirectory : ObjectId}
    (actual : ActorStep runtime (.launch actor references closeExec workingDirectory) before after) :
    after.actors actor = some (.initialFrom sourceProgram references closeExec workingDirectory) := by
  cases actual
  simp only [Population.launch, Population.install, ite_eq_left]

theorem native_handoff_actor_present {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {tick : ActorTick runtime} {processes : NativeProcesses} (source : NativeHandoffAt tick processes) :
    tick.after.actors source.actor = some (.initialFrom sourceProgram source.execution.references.rawProjection.handles
      source.execution.references.rawProjection.closeOnExec source.execution.references.workingDirectory) :=
  launch_actor_present (source.action ▸ tick.operation)

theorem native_handoff_birth {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {before after : Processes} {initial current : NativeProcesses}
    {ticks : List (ActorTick runtime)}
    (journal : NativeExternalJournal process child native hostUid before initial ticks after current)
    {tick : ActorTick runtime} (handoff : NativeHandoffAt tick current)
    (unborn : initial.allocated handoff.actor = false) :
    Nonempty (NativeBirthCut process child native hostUid before after initial current ticks handoff.actor) :=
  native_first_birth journal unborn handoff.active

end LeanCage.Host.Kernel
