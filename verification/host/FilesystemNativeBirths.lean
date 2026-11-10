import FilesystemNativeEffects

namespace LeanCage.Host.Kernel
open Filesystem

variable {sourceProgram : Program UInt32}

structure NativeBirthCut {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (process : ProcessContract runtime) (child : ChildPrimitive kernel)
    (native : NativePrimitive kernel) (hostUid : Nat)
    (before after : Processes) (callers next : NativeProcesses)
    (ticks : List (ActorTick runtime)) (token : NativeToken) where
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
  fresh : priorNative.allocated token = false
  born : nextNative.allocated token = true
  arguments : NativeSpawn
  birth : NativeBirth
  operation : call.operation = .spawn arguments
  product : call.product = .created token
  stored : nextNative.births token = some birth
  parent : birth.parent = call.token
  actualArguments : birth.arguments = arguments

-- §FS-host-boundary.ownership: An actual native birth comes from the same earlier spawn row,
-- including a child created before an error or lost acknowledgement.
theorem native_first_birth {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat}
    {before after : Processes} {callers next : NativeProcesses} {ticks : List (ActorTick runtime)}
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    {token : NativeToken} (absent : callers.allocated token = false) (present : next.allocated token = true) :
    Nonempty (NativeBirthCut process child native hostUid before after callers next ticks token) := by
  induction journal with
  | nil => rw [absent] at present; cases present
  | @cons before middle after callers next final tick ticks actual tail ih =>
    cases allocated : next.allocated token with
    | false =>
      obtain ⟨cut⟩ := ih allocated present
      exact ⟨{
        cut with
        position := cut.position + 1
        selected := by simpa using cut.selected
        bound := by simpa only [List.length_cons] using Nat.add_lt_add_right cut.bound 1
        leading := tick :: cut.leading
        count := by simp only [List.length_cons, cut.count, Nat.add_comm]
        trace := by simp only [cut.trace, List.cons_append]
        first := .cons actual cut.first }⟩
    | true =>
      cases actual with
      | application | ordinary | child => rw [absent] at allocated; cases allocated
      | launch =>
        change callers.allocated token = true at allocated
        rw [absent] at allocated
        cases allocated
      | retiring recorded exit =>
        rw [exit.next] at allocated
        change callers.allocated token = true at allocated
        rw [absent] at allocated
        cases allocated
      | native recorded call retirementFrame =>
        obtain ⟨arguments, birth, operation, product, stored, parent, actualArguments⟩ :=
          native.fresh_source _ _ _ _ _ _ _ _ _ _ call.native absent allocated
        exact ⟨{
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
          fresh := absent
          born := allocated
          arguments
          birth
          operation
          product
          stored
          parent
          actualArguments }⟩

theorem native_birth_retained {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel}
    {native : NativePrimitive kernel} {hostUid : Nat}
    {before after : Processes} {callers next : NativeProcesses} {ticks : List (ActorTick runtime)}
    {token : NativeToken} (cut : NativeBirthCut process child native hostUid before after callers next ticks token) :
    next.births token = some cut.birth :=
  native_journal_birth_frame cut.last cut.stored

end LeanCage.Host.Kernel
