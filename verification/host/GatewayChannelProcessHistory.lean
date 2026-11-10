import GatewayChannelReferences

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat}

-- §AR-host-boundary.primitives: Count actual image replacements, including
-- a repeated exec of the same image. Source activation cannot be identified
-- from the image object's identity alone.
noncomputable def nativeExecIncrement {before after : Processes} {callers next : NativeProcesses}
    {tick : ActorTick runtime}
    (row : NativeExternalStep process child native hostUid before callers tick after next)
    (query : NativeToken) : Nat :=
  match row with
  | .native _ call _ _ =>
    match call.product with
    | .executed _ => if call.token = query then 1 else 0
    | _ => 0
  | _ => 0

noncomputable def nativeExecCountBefore {before after : Processes} {callers next : NativeProcesses}
    {ticks : List (ActorTick runtime)}
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    (position : Nat) (query : NativeToken) : Nat :=
  match journal, position with
  | .nil _ _, _ => 0
  | .cons _ _, 0 => 0
  | .cons row tail, index + 1 => nativeExecIncrement row query + nativeExecCountBefore tail index query

-- This is an actual indexed occurrence in the supplied journal value; it
-- retains its stored NativeCallAt instead of choosing another equal tick.
inductive NativeExecAt (query : NativeToken) :
    {before after : Processes} → {callers next : NativeProcesses} → {ticks : List (ActorTick runtime)} →
    NativeExternalJournal process child native hostUid before callers ticks after next → Nat → Prop where
  | here {before middle after : Processes} {callers next final : NativeProcesses}
      {tick : ActorTick runtime} {ticks : List (ActorTick runtime)}
      (row : NativeExternalStep process child native hostUid before callers tick middle next)
      (tail : NativeExternalJournal process child native hostUid middle next ticks after final)
      (executed : nativeExecIncrement row query = 1) : NativeExecAt query (.cons row tail) 0
  | later {before middle after : Processes} {callers next final : NativeProcesses}
      {tick : ActorTick runtime} {ticks : List (ActorTick runtime)}
      (row : NativeExternalStep process child native hostUid before callers tick middle next)
      (tail : NativeExternalJournal process child native hostUid middle next ticks after final)
      (position : Nat) (executed : NativeExecAt query tail position) : NativeExecAt query (.cons row tail) (position + 1)

theorem native_exec_count_monotone {before after : Processes} {callers next : NativeProcesses}
    {ticks : List (ActorTick runtime)}
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    (query : NativeToken) (first last : Nat) (ordered : first ≤ last) :
    nativeExecCountBefore journal first query ≤ nativeExecCountBefore journal last query := by
  induction journal generalizing first last with
  | nil => exact Nat.le_refl _
  | cons row tail ih =>
    cases first with
    | zero => simp only [nativeExecCountBefore]; exact Nat.zero_le _
    | succ first =>
      cases last with
      | zero => omega
      | succ last =>
        simp only [nativeExecCountBefore]
        exact Nat.add_le_add_left (ih first last (by omega)) _

theorem native_exec_at_increment {before after : Processes} {callers next : NativeProcesses}
    {ticks : List (ActorTick runtime)}
    {journal : NativeExternalJournal process child native hostUid before callers ticks after next}
    {query position : Nat} (executed : NativeExecAt query journal position) :
    nativeExecCountBefore journal position query < nativeExecCountBefore journal (position + 1) query := by
  induction executed with
  | here row tail actual => simp only [nativeExecCountBefore, actual]; omega
  | later row tail position executed ih => simp only [nativeExecCountBefore]; omega

-- §FS-host-boundary.ownership: Matching source incarnations at two actual
-- resumptions exclude an intervening exec, even to the same binary. No future
-- SDK return or cleanup observation is supplied to a pending operation.
theorem same_source_incarnation_no_exec {before after : Processes} {callers next : NativeProcesses}
    {ticks : List (ActorTick runtime)}
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    (query first last : Nat)
    (same : nativeExecCountBefore journal first query = nativeExecCountBefore journal last query)
    (selected : Nat) (lower : first ≤ selected) (upper : selected < last) :
    ¬ NativeExecAt query journal selected := by
  intro executed
  have increment := native_exec_at_increment executed
  have before := native_exec_count_monotone journal query first selected lower
  have after := native_exec_count_monotone journal query (selected + 1) last (by omega)
  omega

theorem native_row_owned_backwards {before after : Processes} {callers next : NativeProcesses}
    {tick : ActorTick runtime}
    (row : NativeExternalStep process child native hostUid before callers tick after next)
    (query : NativeToken) (alive : next.nativeOwned query = true) : callers.nativeOwned query = true := by
  cases row with
  | application | ordinary | child => exact alive
  | launch recorded handoff =>
    by_cases same : query = handoff.actor
    · simp only [NativeProcesses.transfer, same, ite_true] at alive
      contradiction
    · simpa only [NativeProcesses.transfer, ite_eq_right same] using alive
  | native recorded call retiring others =>
    have same := native.native_ownership _ _ _ _ _ _ _ _ _ call.native
    rw [same] at alive
    exact alive
  | retiring recorded exit =>
    rw [exit.next] at alive
    by_cases same : query = exit.token
    · simp only [NativeProcesses.retire, same, ite_true] at alive
      contradiction
    · simpa only [NativeProcesses.retire, ite_eq_right same] using alive

theorem native_journal_owned_backwards {before after : Processes} {callers next : NativeProcesses}
    {ticks : List (ActorTick runtime)}
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    (query : NativeToken) (alive : next.nativeOwned query = true) : callers.nativeOwned query = true := by
  induction journal with
  | nil => exact alive
  | cons row tail ih => exact native_row_owned_backwards row query (ih alive)

-- A selected still-native activation excludes an earlier handoff/retirement,
-- while every actual process/image and descriptor effect remains in the row.
theorem selected_native_owned_before {before after : Processes} {callers next : NativeProcesses}
    {ticks : List (ActorTick runtime)}
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    (query : NativeToken) (alive : next.nativeOwned query = true)
    {position : Nat}
    (point : SelectedNativeCut process child native hostUid before after callers next ticks position)
    (_same : selectNativeCut journal position = some point) :
    point.cut.priorNative.nativeOwned query = true ∧ point.cut.nextNative.nativeOwned query = true := by
  have after := native_journal_owned_backwards point.cut.last query alive
  exact ⟨native_row_owned_backwards point.cut.current query after, after⟩

theorem native_exec_before_zero {before after : Processes} {callers next : NativeProcesses}
    {ticks : List (ActorTick runtime)}
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next) (query : NativeToken) :
    nativeExecCountBefore journal 0 query = 0 := by cases journal <;> rfl

theorem selected_native_exec_increment {before after : Processes} {callers next : NativeProcesses}
    {ticks : List (ActorTick runtime)}
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    (query : NativeToken) {position : Nat}
    (point : SelectedNativeCut process child native hostUid before after callers next ticks position)
    (same : selectNativeCut journal position = some point) :
    nativeExecCountBefore journal (position + 1) query = nativeExecCountBefore journal position query +
      nativeExecIncrement point.cut.current query := by
  induction journal generalizing position with
  | nil => cases same
  | @cons before middle after callers next final tick ticks row tail ih =>
    cases position with
    | zero =>
      have identity : point = ⟨tick, ⟨[], ticks, rfl, rfl, before, middle, callers, next, .nil _ _, row, tail⟩⟩ :=
        (Option.some.inj same).symm
      cases identity
      simp only [nativeExecCountBefore, native_exec_before_zero, Nat.add_zero, Nat.zero_add]
    | succ position =>
      let extend := fun (chosen : SelectedNativeCut process child native hostUid middle after next final ticks position) =>
        ({ tick := chosen.tick
           cut := { chosen.cut with
             leading := tick :: chosen.cut.leading
             count := by simp only [List.length_cons, chosen.cut.count]
             shape := by simp only [chosen.cut.shape, List.cons_append]
             first := .cons row chosen.cut.first } } :
          SelectedNativeCut process child native hostUid before after callers final (tick :: ticks) (position + 1))
      change (selectNativeCut tail position).map extend = some point at same
      cases earlier : selectNativeCut tail position with
      | none => simp only [earlier, Option.map_none] at same; cases same
      | some chosen =>
        have increase := ih chosen earlier
        simp only [earlier, Option.map_some] at same
        have identity := (Option.some.inj same).symm
        cases identity
        simp only [nativeExecCountBefore]
        simpa only [Nat.add_assoc] using congrArg (nativeExecIncrement row query + ·) increase

theorem selected_exec_excluded_by_incarnation {before after : Processes} {callers next : NativeProcesses}
    {ticks : List (ActorTick runtime)}
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    (query first last : Nat)
    (sameIncarnation : nativeExecCountBefore journal first query = nativeExecCountBefore journal last query)
    {position : Nat}
    (point : SelectedNativeCut process child native hostUid before after callers next ticks position)
    (same : selectNativeCut journal position = some point)
    (lower : first ≤ position) (upper : position < last) : nativeExecIncrement point.cut.current query = 0 := by
  have increase := selected_native_exec_increment journal query point same
  have before := native_exec_count_monotone journal query first position lower
  have after := native_exec_count_monotone journal query (position + 1) last (by omega)
  omega

end LeanCage.Host.PrivateStreams
