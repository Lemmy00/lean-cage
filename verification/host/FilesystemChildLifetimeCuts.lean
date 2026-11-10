import FilesystemChildLifetimes
import GatewayChannelHistory

namespace LeanCage.Host.Kernel
open PrivateStreams

-- §FS-host-boundary.ownership: Reuse the checked structural selector on the
-- exact journal value. The resulting lifecycle cut retains that head's
-- embedded call and tables, including repeated equal-looking ticks.
theorem selected_child_lifecycle {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {process : ProcessContract runtime}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {laws : ChildLifecycleContract process child native hostUid}
    {before after : Processes} {first last : NativeProcesses} {ticks : List (ActorTick runtime)}
    {recording : NativeExternalJournal process child native hostUid before first ticks after last}
    {prior final : ReapedChildren} (journal : ChildLifecycleJournal laws recording prior final)
    {position : Nat}
    (selected : SelectedNativeCut process child native hostUid before after first last ticks position)
    (same : selectNativeCut recording position = some selected) :
    ∃ intermediate next,
      ChildLifecycleJournal laws selected.cut.first prior intermediate ∧
      laws.observed selected.cut.current intermediate next ∧
      ChildLifecycleJournal laws selected.cut.last next final := by
  induction journal generalizing position with
  | nil => cases same
  | @cons before middle after first next last tick ticks current rest prior intermediate final observed tail ih =>
    cases position with
    | zero =>
      have identity := Option.some.inj same
      cases identity
      exact ⟨prior, intermediate, .nil _, observed, tail⟩
    | succ position =>
      let extend (previous : SelectedNativeCut process child native hostUid middle after next last ticks position) :
          SelectedNativeCut process child native hostUid before after first last (tick :: ticks) (position + 1) :=
        ⟨previous.tick, {
          previous.cut with
          leading := tick :: previous.cut.leading
          count := by simp only [List.length_cons, previous.cut.count]
          shape := by simp only [previous.cut.shape, List.cons_append]
          first := .cons current previous.cut.first }⟩
      change (selectNativeCut rest position).map extend = some selected at same
      cases choice : selectNativeCut rest position with
      | none =>
        rw [choice, Option.map_none] at same
        cases same
      | some previous =>
        rw [choice, Option.map_some] at same
        have identity := Option.some.inj same
        cases identity
        obtain ⟨atPrevious, afterPrevious, leading, actual, following⟩ := ih previous choice
        exact ⟨atPrevious, afterPrevious, .cons observed leading, actual, following⟩

-- §FS-host-boundary.ownership: A selected real wait excludes future actions
-- of its exact owned token. The source/SDK adapter must supply this head's
-- captured lease; structural Child/PID equality alone is insufficient.
theorem actual_reaping_excludes_child_tail {kernel : Contract} {sourceProgram : Program UInt32}
    {runtime : ActorRuntime kernel sourceProgram} {process : ProcessContract runtime}
    {child : ChildPrimitive kernel} {native : NativePrimitive kernel} {hostUid : Nat}
    {laws : ChildLifecycleContract process child native hostUid}
    {before after : Processes} {first last : NativeProcesses} {ticks : List (ActorTick runtime)}
    {recording : NativeExternalJournal process child native hostUid before first ticks after last}
    {prior final : ReapedChildren} (journal : ChildLifecycleJournal laws recording prior final)
    {position : Nat}
    (selected : SelectedNativeCut process child native hostUid before after first last ticks position)
    (same : selectNativeCut recording position = some selected)
    {all : List (ActorTick runtime)} {arguments : IO.Process.SpawnArgs}
    {value : IO.Process.Child arguments.toStdioConfig}
    (lease : SpawnedChildLease process all arguments value)
    (captured : laws.usesLease selected.cut.current lease.key) (use : ReapingUse lease selected.tick.action) :
    selected.cut.last.NoChildToken lease.token ∧ final lease.token = true := by
  obtain ⟨atCurrent, afterCurrent, leading, observed, following⟩ := selected_child_lifecycle journal selected same
  exact reaping_head_excludes_child_tail observed following lease captured use

end LeanCage.Host.Kernel
