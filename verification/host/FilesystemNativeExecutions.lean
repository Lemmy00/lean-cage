import FilesystemNativeHandoff

namespace LeanCage.Host.Kernel
open Filesystem

variable {sourceProgram : Program UInt32}

structure NativeExecutionCut {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (process : ProcessContract runtime) (child : ChildPrimitive kernel)
    (native : NativePrimitive kernel) (hostUid : Nat)
    (before after : Processes) (callers next : NativeProcesses)
    (ticks : List (ActorTick runtime)) (token : NativeToken) (execution : NativeExecution) where
  position : Nat
  tick : ActorTick runtime
  selected : ticks[position]? = some tick
  bound : position < ticks.length
  leading : List (ActorTick runtime)
  trailing : List (ActorTick runtime)
  count : position = leading.length
  trace : ticks = leading ++ tick :: trailing
  priorProcesses : Processes
  nextProcesses : Processes
  priorNative : NativeProcesses
  nextNative : NativeProcesses
  first : NativeExternalJournal process child native hostUid before callers leading priorProcesses priorNative
  recorded : process.step tick priorProcesses nextProcesses
  call : NativeCallAt native tick priorNative nextNative
  last : NativeExternalJournal process child native hostUid nextProcesses nextNative trailing after next
  identity : call.token = token
  product : call.product = .executed execution.image
  stored : nextNative.executions token = some execution

-- §FS-host-boundary.caller: A stored image observation has an actual earlier exec row, or was
-- already present at the initialized boundary. Spawn success is never substituted for exec.
theorem native_execution_source {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat}
    {before after : Processes} {callers next : NativeProcesses} {ticks : List (ActorTick runtime)}
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    {token : NativeToken} {execution : NativeExecution} (stored : next.executions token = some execution) :
    callers.executions token = some execution ∨
      Nonempty (NativeExecutionCut process child native hostUid before after callers next ticks token execution) := by
  induction journal with
  | nil => exact .inl stored
  | @cons before middle after callers next final tick ticks actual tail ih =>
    rcases ih stored with current | later
    · cases actual with
      | application | launch | ordinary | child => exact .inl current
      | retiring recorded exit => rw [exit.next] at current; exact .inl current
      | native recorded call retirementFrame =>
        rcases native.execution_origin _ _ _ _ _ _ _ _ _ _ _ call.native current with old | ⟨identity, product⟩
        · exact .inl old
        · exact .inr ⟨{
            position := 0
            tick
            selected := rfl
            bound := by simp
            leading := []
            trailing := ticks
            count := rfl
            trace := rfl
            priorProcesses := before
            nextProcesses := middle
            priorNative := callers
            nextNative := next
            first := .nil _ _
            recorded
            call
            last := tail
            identity := identity.symm
            product
            stored := current }⟩
    · obtain ⟨cut⟩ := later
      exact .inr ⟨{
        cut with
        position := cut.position + 1
        selected := by simpa using cut.selected
        bound := by simpa only [List.length_cons] using Nat.add_lt_add_right cut.bound 1
        leading := tick :: cut.leading
        count := by simp only [List.length_cons, cut.count, Nat.add_comm]
        trace := by simp only [cut.trace, List.cons_append]
        first := .cons actual cut.first }⟩

theorem native_execution_actual_table {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat}
    {before after : Processes} {callers next : NativeProcesses} {ticks : List (ActorTick runtime)}
    {token : NativeToken} {execution : NativeExecution}
    (cut : NativeExecutionCut process child native hostUid before after callers next ticks token execution) :
    cut.call.operation = .exec execution.arguments ∧ cut.call.afterReferences = execution.references := by
  obtain ⟨arguments, actual, operation, stored, image, argumentBytes, table⟩ :=
    native_exec_table cut.call cut.product
  have same : actual = execution := Option.some.inj (stored.symm.trans (by simpa only [cut.identity] using cut.stored))
  have argumentsSame : execution.arguments = arguments :=
    (congrArg NativeExecution.arguments same).symm.trans argumentBytes
  exact ⟨operation.trans (congrArg NativeOperation.exec argumentsSame.symm),
    table.trans (congrArg NativeExecution.references same)⟩

theorem native_handoff_execution {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat}
    {before after : Processes} {initial current : NativeProcesses} {ticks : List (ActorTick runtime)}
    (journal : NativeExternalJournal process child native hostUid before initial ticks after current)
    {tick : ActorTick runtime} (handoff : NativeHandoffAt tick current)
    (absent : initial.executions handoff.actor = none) :
    Nonempty (NativeExecutionCut process child native hostUid before after initial current ticks
      handoff.actor handoff.execution) := by
  rcases native_execution_source journal handoff.recorded with earlier | actual
  · rw [absent] at earlier
    cases earlier
  · exact actual

-- §FS-host-boundary.ownership: The same child lifetime was born before its actual exec. The
-- selected birth's local prefix index is also its index in the complete global journal.
theorem native_execution_birth_before {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat}
    {before after : Processes} {callers next : NativeProcesses} {ticks : List (ActorTick runtime)}
    {token : NativeToken} {execution : NativeExecution}
    (cut : NativeExecutionCut process child native hostUid before after callers next ticks token execution)
    (unborn : callers.allocated token = false) :
    ∃ birth : NativeBirthCut process child native hostUid before cut.priorProcesses callers cut.priorNative
      cut.leading token, birth.position < cut.position ∧ ticks[birth.position]? = some birth.tick := by
  have active : cut.priorNative.allocated token = true := by simpa only [cut.identity] using cut.call.active
  obtain ⟨birth⟩ := native_first_birth cut.first unborn active
  refine ⟨birth, by simpa only [cut.count] using birth.bound, ?_⟩
  have sameList := congrArg (fun events => events[birth.position]?) cut.trace
  exact sameList.trans ((List.getElem?_append_left birth.bound).trans birth.selected)

end LeanCage.Host.Kernel
