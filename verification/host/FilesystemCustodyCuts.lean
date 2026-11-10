import FilesystemCustodyExecution
import GatewayChannelHistory

namespace LeanCage.Host.Kernel
open PrivateStreams

-- §FS-host-boundary.ownership: A source/IPC/marker consumer receives the custody
-- snapshot of the exact structurally selected recording head. An equal foreign tick
-- is insufficient to substitute another NativeCallAt or another native FD table.
theorem RegisteredCustodyExecution.selected_before {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
    {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
    {initial : World} {all : List (ActorTick runtime)} {hostUid : Nat}
    {dataObjects directories : ObjectId → Prop} {semantics : NameSemanticsView}
    {before after : Processes} {first last : NativeProcesses} {ticks processed : List (ActorTick runtime)}
    {start finish : Population}
    {recording : NativeExternalJournal process child native hostUid before first ticks after last}
    (source : RegisteredCustodyExecution runtime initial all hostUid dataObjects directories semantics recording
      processed start finish)
    {position : Nat} (selected : SelectedNativeCut process child native hostUid before after first last ticks position)
    (same : selectNativeCut recording position = some selected) :
    ∃ foreignReferences, Nonempty (RegisteredCustodyState runtime initial all hostUid dataObjects directories semantics
      foreignReferences (processed ++ selected.cut.leading) selected.tick.before selected.cut.priorNative) := by
  induction source generalizing position with
  | nil => simp only [selectNativeCut] at same; cases same
  | @cons before middle after first next last tick ticks processed final foreign current rest state tail ih =>
    cases position with
    | zero =>
      have identity : selected = ⟨tick, ⟨[], ticks, rfl, rfl, before, middle, first, next, .nil _ _, current, rest⟩⟩ :=
        (Option.some.inj same).symm
      cases identity
      exact ⟨foreign, ⟨by simpa only [List.append_nil] using state⟩⟩
    | succ position =>
      let extend := fun (chosen : SelectedNativeCut process child native hostUid middle after next last ticks position) =>
        ({ tick := chosen.tick
           cut := { chosen.cut with
             leading := tick :: chosen.cut.leading
             count := by simp only [List.length_cons, chosen.cut.count]
             shape := by simp only [chosen.cut.shape, List.cons_append]
             first := .cons current chosen.cut.first } } :
          SelectedNativeCut process child native hostUid before after first last (tick :: ticks) (position + 1))
      change (selectNativeCut rest position).map extend = some selected at same
      cases earlier : selectNativeCut rest position with
      | none => simp only [earlier, Option.map_none] at same; cases same
      | some chosen =>
        obtain ⟨foreignReferences, ⟨prior⟩⟩ := ih chosen earlier
        simp only [earlier, Option.map_some] at same
        have identity := (Option.some.inj same).symm
        cases identity
        exact ⟨foreignReferences, ⟨by
          simpa only [extend, List.append_assoc, List.singleton_append] using prior⟩⟩

end LeanCage.Host.Kernel
