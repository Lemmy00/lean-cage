import FilesystemNativeAuthority
import GatewayChannelHistory

namespace LeanCage.Host.Kernel
open PrivateStreams

-- §FS-host-boundary.ownership: Authority for a prefix and selected operation is
-- projected from the exact recording value. Equal foreign ticks cannot substitute
-- alternate child operations, native tables or process ledgers.
theorem recorded_authority_at {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {hostUid : Nat} {before after : Processes} {first last : NativeProcesses} {ticks : List (ActorTick runtime)}
    (recording : NativeExternalJournal process child native hostUid before first ticks after last)
    (safe : NativeAuthorityJournal recording) {position : Nat}
    (point : SelectedNativeCut process child native hostUid before after first last ticks position)
    (selected : selectNativeCut recording position = some point) :
    NativeAuthorityJournal point.cut.first ∧ NativeAuthoritySafe point.cut.current ∧ NativeAuthorityJournal point.cut.last := by
  induction recording generalizing position with
  | nil => simp only [selectNativeCut] at selected; cases selected
  | @cons before middle after first next last tick ticks current rest ih =>
    cases position with
    | zero =>
      have same : point = ⟨tick, ⟨[], ticks, rfl, rfl, before, middle, first, next, .nil _ _, current, rest⟩⟩ :=
        (Option.some.inj selected).symm
      cases same
      exact ⟨True.intro, safe.1, safe.2⟩
    | succ position =>
      let extend := fun (chosen : SelectedNativeCut process child native hostUid middle after next last ticks position) =>
        ({ tick := chosen.tick
           cut := { chosen.cut with
             leading := tick :: chosen.cut.leading
             count := by simp only [List.length_cons, chosen.cut.count]
             shape := by simp only [chosen.cut.shape, List.cons_append]
             first := .cons current chosen.cut.first } } :
          SelectedNativeCut process child native hostUid before after first last (tick :: ticks) (position + 1))
      change (selectNativeCut rest position).map extend = some point at selected
      cases earlier : selectNativeCut rest position with
      | none => simp only [earlier, Option.map_none] at selected; cases selected
      | some chosen =>
        obtain ⟨leading, currentSafe, trailing⟩ := ih safe.2 chosen earlier
        simp only [earlier, Option.map_some] at selected
        have identity := (Option.some.inj selected).symm
        cases identity
        exact ⟨⟨safe.1, leading⟩, currentSafe, trailing⟩

end LeanCage.Host.Kernel
