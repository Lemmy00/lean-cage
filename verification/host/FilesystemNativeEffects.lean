import FilesystemChildEffects

namespace LeanCage.Host.Kernel
open Filesystem

variable {sourceProgram : Program UInt32}

-- §FS-host-boundary.ownership: This joint row keeps the source-owned child registry and native
-- caller registry on the same actual tick, without changing ActorAction.
inductive NativeExternalStep {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (process : ProcessContract runtime) (child : ChildPrimitive kernel)
    (native : NativePrimitive kernel) (hostUid : Nat) :
    Processes → NativeProcesses → ActorTick runtime → Processes → NativeProcesses → Type 1 where
  | application {before after : Processes} {callers : NativeProcesses} {tick : ActorTick runtime}
      (recorded : process.step tick before after)
      (notForeign : ∀ caller, tick.action ≠ .foreign caller)
      (notLaunch : ∀ actor references closeExec workingDirectory,
        tick.action ≠ .launch actor references closeExec workingDirectory)
      (notRetiring : ∀ token observation beforeResources afterResources,
        tick.action ≠ .nativeRetire token observation beforeResources afterResources) :
      NativeExternalStep process child native hostUid before callers tick after callers
  | launch {before after : Processes} {callers : NativeProcesses} {tick : ActorTick runtime}
      (recorded : process.step tick before after) (handoff : NativeHandoffAt tick callers) :
      NativeExternalStep process child native hostUid before callers tick after
        (callers.transfer handoff.actor handoff.execution)
  | ordinary {before after : Processes} {callers : NativeProcesses} {tick : ActorTick runtime}
      (caller : Credentials) (recorded : process.step tick before after)
      (action : tick.action = .foreign caller) (allowed : OrdinaryForeign caller hostUid) :
      NativeExternalStep process child native hostUid before callers tick after callers
  | child {before after : Processes} {callers : NativeProcesses} {tick : ActorTick runtime}
      (recorded : process.step tick before after) (call : ChildCallAt child tick before after) :
      NativeExternalStep process child native hostUid before callers tick after callers
  | native {before after : Processes} {callers next : NativeProcesses} {tick : ActorTick runtime}
      (recorded : process.step tick before after) (call : NativeCallAt native tick callers next)
      (retirementFrame : next.retiring = callers.retiring)
      (otherReferences : ∀ token, token ≠ call.token → callers.allocated token = true →
        next.references token = callers.references token) :
      NativeExternalStep process child native hostUid before callers tick after next
  | retiring {before after : Processes} {callers next : NativeProcesses} {tick : ActorTick runtime}
      (recorded : process.step tick before after) (exit : NativeRetirementAt tick callers next) :
      NativeExternalStep process child native hostUid before callers tick after next

def NativeExternalStep.external {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat}
    {before after : Processes} {callers next : NativeProcesses} {tick : ActorTick runtime}
    (step : NativeExternalStep process child native hostUid before callers tick after next) :
    ExternalStep process child hostUid before tick after (some native) := by
  cases step with
  | application recorded notForeign notLaunch => exact .application recorded notForeign
  | launch recorded handoff =>
    exact .application recorded (by intro caller impossible; rw [handoff.action] at impossible; cases impossible)
  | ordinary caller recorded action allowed => exact .ordinary caller recorded action allowed
  | child recorded call => exact .child recorded call
  | native recorded call retirementFrame => exact .native recorded native rfl call
  | retiring recorded exit => exact .application recorded (by
      intro caller impossible
      rw [exit.action] at impossible
      cases impossible)

theorem NativeExternalStep.monotone {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat}
    {before after : Processes} {callers next : NativeProcesses} {tick : ActorTick runtime}
    (step : NativeExternalStep process child native hostUid before callers tick after next)
    (token : NativeToken) (allocated : callers.allocated token = true) : next.allocated token = true := by
  cases step with
  | application | launch | ordinary | child => exact allocated
  | native recorded call retirementFrame => exact native.allocation_monotone _ _ _ _ _ _ _ _ _ _ call.native allocated
  | retiring recorded exit => rw [exit.next]; exact allocated

theorem NativeExternalStep.birth_frame {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat}
    {before after : Processes} {callers next : NativeProcesses} {tick : ActorTick runtime}
    (step : NativeExternalStep process child native hostUid before callers tick after next)
    {token : NativeToken} {birth : NativeBirth} (present : callers.births token = some birth) :
    next.births token = some birth := by
  cases step with
  | application | launch | ordinary | child => exact present
  | native recorded call retirementFrame => exact native.birth_frame _ _ _ _ _ _ _ _ _ _ _ call.native present
  | retiring recorded exit => rw [exit.next]; exact present

-- §AR-host-boundary.primitives: Only native rows update the native process table. Mutable OFD
-- positions and shared storage remain in each actual World, not in that process table.
inductive NativeExternalJournal {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (process : ProcessContract runtime) (child : ChildPrimitive kernel)
    (native : NativePrimitive kernel) (hostUid : Nat) :
    Processes → NativeProcesses → List (ActorTick runtime) → Processes → NativeProcesses → Type 1 where
  | nil (processes : Processes) (callers : NativeProcesses) :
      NativeExternalJournal process child native hostUid processes callers [] processes callers
  | cons {before middle after : Processes} {callers next final : NativeProcesses}
      {tick : ActorTick runtime} {ticks : List (ActorTick runtime)}
      (actual : NativeExternalStep process child native hostUid before callers tick middle next)
      (tail : NativeExternalJournal process child native hostUid middle next ticks after final) :
      NativeExternalJournal process child native hostUid before callers (tick :: ticks) after final

def NativeExternalJournal.external {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat}
    {before after : Processes} {callers next : NativeProcesses} {ticks : List (ActorTick runtime)}
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next) :
    ExternalJournal process child hostUid before ticks after (some native) :=
  match journal with
  | .nil _ _ => .nil _
  | .cons actual tail => .cons actual.external tail.external

theorem native_journal_monotone {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat}
    {before after : Processes} {callers next : NativeProcesses} {ticks : List (ActorTick runtime)}
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    (token : NativeToken) (allocated : callers.allocated token = true) : next.allocated token = true := by
  induction journal with
  | nil => exact allocated
  | cons actual tail ih => exact ih (actual.monotone token allocated)

theorem native_journal_birth_frame {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat}
    {before after : Processes} {callers next : NativeProcesses} {ticks : List (ActorTick runtime)}
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    {token : NativeToken} {birth : NativeBirth} (present : callers.births token = some birth) :
    next.births token = some birth := by
  induction journal with
  | nil => exact present
  | cons actual tail ih => exact ih (actual.birth_frame present)

structure NativeExternalCut {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (process : ProcessContract runtime) (child : ChildPrimitive kernel)
    (native : NativePrimitive kernel) (hostUid : Nat)
    (before after : Processes) (callers next : NativeProcesses)
    (ticks : List (ActorTick runtime)) (position : Nat) (tick : ActorTick runtime) where
  leading : List (ActorTick runtime)
  trailing : List (ActorTick runtime)
  count : position = leading.length
  shape : ticks = leading ++ tick :: trailing
  priorProcesses : Processes
  nextProcesses : Processes
  priorNative : NativeProcesses
  nextNative : NativeProcesses
  first : NativeExternalJournal process child native hostUid before callers leading priorProcesses priorNative
  current : NativeExternalStep process child native hostUid priorProcesses priorNative tick nextProcesses nextNative
  last : NativeExternalJournal process child native hostUid nextProcesses nextNative trailing after next

-- §FS-host-boundary.acceptance: Selection preserves the same global position and both tables.
theorem native_selected_cut {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat}
    {before after : Processes} {callers next : NativeProcesses} {ticks : List (ActorTick runtime)}
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    {position : Nat} {tick : ActorTick runtime} (selected : ticks[position]? = some tick) :
    Nonempty (NativeExternalCut process child native hostUid before after callers next ticks position tick) := by
  induction journal generalizing position with
  | nil => cases selected
  | @cons before middle after callers next final first ticks actual tail ih =>
    cases position with
    | zero =>
      have same := Option.some.inj selected
      subst first
      exact ⟨⟨[], ticks, rfl, rfl, before, middle, callers, next, .nil _ _, actual, tail⟩⟩
    | succ position =>
      obtain ⟨cut⟩ := ih selected
      exact ⟨{
        cut with
        leading := first :: cut.leading
        count := by simpa only [List.length_cons] using congrArg Nat.succ cut.count
        shape := by simp only [cut.shape, List.cons_append]
        first := .cons actual cut.first }⟩

-- §FS-host-boundary.caller: An exec observation retains this lifetime's actual post-exec table.
theorem native_exec_table {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {primitive : NativePrimitive kernel}
    {tick : ActorTick runtime} {before after : NativeProcesses}
    (call : NativeCallAt primitive tick before after) {image : ObjectId}
    (executed : call.product = .executed image) :
    ∃ arguments execution, call.operation = .exec arguments ∧
      after.executions call.token = some execution ∧ execution.image = image ∧
      execution.arguments = arguments ∧ call.afterReferences = execution.references := by
  obtain ⟨arguments, execution, operation, stored, actualImage, actualArguments, table⟩ :=
    primitive.exec_source _ _ _ _ _ _ _ _ _ _ call.native executed
  exact ⟨arguments, execution, operation, stored, actualImage, actualArguments,
    Option.some.inj (call.outputTable.symm.trans table)⟩

end LeanCage.Host.Kernel
