import GatewayStreamSources

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

variable {kernel : Contract} {sourceProgram : Program UInt32}
  {runtime : ActorRuntime kernel sourceProgram}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {ticks : List (ActorTick runtime)}

structure SelectedNativeCut (process : ProcessContract runtime) (child : ChildPrimitive kernel)
    (native : NativePrimitive kernel) (hostUid : Nat) (before after : Processes)
    (callers next : NativeProcesses) (ticks : List (ActorTick runtime)) (position : Nat) where
  tick : ActorTick runtime
  cut : NativeExternalCut process child native hostUid before after callers next ticks position tick

-- §AR-host-boundary.interfaces.gateway: Select from this journal's stored row.
-- Equal ticks alone must not select another valid native-call witness.
noncomputable def selectNativeCut
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next) :
    (position : Nat) →
    Option (SelectedNativeCut process child native hostUid before after callers next ticks position) := by
  induction journal with
  | nil => intro position; exact none
  | @cons before middle after callers following next tick rest actual tail ih =>
    exact fun
    | 0 => some ⟨tick, ⟨[], rest, rfl, rfl, before, middle, callers, following, .nil _ _, actual, tail⟩⟩
    | position + 1 => (ih position).map fun selected =>
        ⟨selected.tick, {
          selected.cut with
          leading := tick :: selected.cut.leading
          count := by simp only [List.length_cons, selected.cut.count]
          shape := by simp only [selected.cut.shape, List.cons_append]
          first := .cons actual selected.cut.first }⟩

theorem selectNativeCut_exists
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    {position : Nat} {tick : ActorTick runtime} (selected : ticks[position]? = some tick) :
    ∃ cut, selectNativeCut journal position = some ⟨tick, cut⟩ := by
  induction journal generalizing position with
  | nil => cases selected
  | @cons before middle after callers following next first rest actual tail ih =>
    cases position with
    | zero =>
      have same := Option.some.inj selected
      subst first
      exact ⟨_, rfl⟩
    | succ position =>
      obtain ⟨cut, same⟩ := ih selected
      simp only [selectNativeCut] at same
      simp only [selectNativeCut, same, Option.map_some]
      exact ⟨_, rfl⟩

def SameNativeCut
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    {position : Nat} {tick : ActorTick runtime}
    (cut : NativeExternalCut process child native hostUid before after callers next ticks position tick) : Prop :=
  selectNativeCut journal position = some ⟨tick, cut⟩

theorem sameNativeCut_unique
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    {position : Nat} {first last : SelectedNativeCut process child native hostUid before after callers next ticks position}
    (left : selectNativeCut journal position = some first)
    (right : selectNativeCut journal position = some last) : first = last :=
  Option.some.inj (left.symm.trans right)

-- §FS-host-boundary.ownership: Every physical channel entry retains the exact
-- journal selector, including all prior/next native and process tables.
def ActualPairBirth {runtime : PrimitiveActorRuntime kernel} {process : ProcessContract runtime}
    {ticks : List (ActorTick runtime)} {pair : Pair}
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    (entry : PairBirthEntry process child native hostUid before after callers next ticks pair) : Prop :=
  SameNativeCut journal entry.cut

def ActualNativeRead {runtime : PrimitiveActorRuntime kernel} {process : ProcessContract runtime}
    {ticks : List (ActorTick runtime)} {pair : Pair}
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    (entry : NativeReadEntry process child native hostUid before after callers next ticks pair) : Prop :=
  SameNativeCut journal entry.cut

def ActualNativeWrite {runtime : PrimitiveActorRuntime kernel} {process : ProcessContract runtime}
    {ticks : List (ActorTick runtime)} {pair : Pair}
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    (entry : NativeWriteEntry process child native hostUid before after callers next ticks pair) : Prop :=
  SameNativeCut journal entry.cut

end LeanCage.Host.PrivateStreams
