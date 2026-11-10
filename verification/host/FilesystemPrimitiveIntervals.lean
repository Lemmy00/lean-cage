import FilesystemIntervals

namespace LeanCage.Host.Kernel

variable {sourceProgram : Program UInt32}

-- §FS-host-boundary.acceptance: The interval begins after the actual returned sample and ends
-- before the selected later call, preserving both endpoint ticks and their global positions.
theorem journal_between_after_counted {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {before after : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime before all after) {first second : Nat} {left right : ActorTick runtime}
    (leftAt : all[first]? = some left) (rightAt : all[second]? = some right) (ordered : first < second) :
    ∃ leading inside trailing, all = leading ++ left :: inside ++ right :: trailing ∧
      leading.length = first ∧ leading.length + 1 + inside.length = second ∧
      ActorJournal runtime left.after inside right.before := by
  obtain ⟨leading, rest, firstTrace, firstCount, prior⟩ := journal_selected_prefix journal leftAt
  have arranged := journal
  rw [firstTrace] at arranged
  obtain ⟨middle, initial, remaining⟩ := actor_journal_split leading _ arranged
  have later : leading.length ≤ second := by omega
  have offset : second - leading.length = (second - leading.length - 1) + 1 := by omega
  have rightRest : rest[second - leading.length - 1]? = some right := by
    have selected : (left :: rest)[second - leading.length]? = some right := by
      simpa only [firstTrace, List.getElem?_append_right later] using rightAt
    rw [offset] at selected
    exact selected
  cases remaining with
  | cons tail =>
    obtain ⟨inside, trailing, lastTrace, lastCount, region⟩ := journal_selected_prefix tail rightRest
    refine ⟨leading, inside, trailing, ?_, firstCount, ?_, region⟩
    · rw [firstTrace, lastTrace]
      simp only [List.cons_append, List.append_assoc]
    · omega

theorem journal_between_after {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {before after : Population} {all : List (ActorTick runtime)}
    (journal : ActorJournal runtime before all after) {first second : Nat} {left right : ActorTick runtime}
    (leftAt : all[first]? = some left) (rightAt : all[second]? = some right) (ordered : first < second) :
    ∃ leading inside trailing, all = leading ++ left :: inside ++ right :: trailing ∧
      leading.length = first ∧ ActorJournal runtime left.after inside right.before := by
  obtain ⟨leading, inside, trailing, trace, firstCount, lastCount, region⟩ :=
    journal_between_after_counted journal leftAt rightAt ordered
  exact ⟨leading, inside, trailing, trace, firstCount, region⟩

end LeanCage.Host.Kernel
