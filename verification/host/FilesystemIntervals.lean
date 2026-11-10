import FilesystemMarkerGuards
import FilesystemReferenceLifetime

namespace LeanCage.Host.Kernel

variable {sourceProgram : Program UInt32}

-- §FS-host-boundary.acceptance: Keep exact positions and the original tick list during slicing.
theorem journal_selected_prefix {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {before after : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime before ticks after) {position : Nat} {tick : ActorTick runtime}
    (selected : ticks[position]? = some tick) :
    ∃ leading trailing, ticks = leading ++ tick :: trailing ∧ leading.length = position ∧
      ActorJournal runtime before leading tick.before := by
  induction position generalizing before ticks with
  | zero =>
    cases journal with
    | nil => cases selected
    | @cons first ticks after remaining =>
      have same : first = tick := Option.some.inj selected
      subst first
      exact ⟨[], ticks, rfl, rfl, .nil _⟩
  | succ position ih =>
    cases journal with
    | nil => cases selected
    | @cons first ticks after remaining =>
      obtain ⟨leading, trailing, shape, count, initial⟩ := ih remaining selected
      exact ⟨first :: leading, trailing, by rw [shape]; rfl, by simp only [List.length_cons, count],
        .cons initial⟩

-- §FS-host-boundary.ownership: A held interval consists of the same global syscall ticks.
theorem journal_between_selected {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {before after : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime before ticks after) {first second : Nat} {left right : ActorTick runtime}
    (leftAt : ticks[first]? = some left) (rightAt : ticks[second]? = some right) (ordered : first ≤ second) :
    ∃ leading inside trailing, ticks = leading ++ inside ++ trailing ∧
      ActorJournal runtime left.before inside right.before := by
  obtain ⟨leading, rest, shape, count, initial⟩ := journal_selected_prefix journal leftAt
  have arranged := journal
  rw [shape] at arranged
  obtain ⟨middle, _, remaining⟩ := actor_journal_split leading _ arranged
  have rightSelected : (left :: rest)[second - leading.length]? = some right := by
    have later : leading.length ≤ second := by omega
    simpa only [shape, List.getElem?_append_right later] using rightAt
  obtain ⟨inside, trailing, regionShape, regionCount, region⟩ := journal_selected_prefix remaining rightSelected
  cases remaining with
  | cons tail =>
    exact ⟨leading, inside, right :: trailing, by rw [shape, regionShape, List.append_assoc], region⟩

theorem safe_external_split {kernel : Contract} {runtime : ActorRuntime kernel}
    {contract : ProcessContract runtime} {primitive : ChildPrimitive kernel} {hostUid : Nat}
    {before after : Processes} (first last : List (ActorTick runtime))
    (recording : ExternalJournal contract primitive hostUid before (first ++ last) after)
    (safe : ExternalAuthorityJournal recording) :
    ∃ middle, ∃ initial : ExternalJournal contract primitive hostUid before first middle,
      ∃ final : ExternalJournal contract primitive hostUid middle last after,
        ExternalAuthorityJournal initial ∧ ExternalAuthorityJournal final := by
  induction first generalizing before with
  | nil => exact ⟨before, .nil _, recording, True.intro, safe⟩
  | cons tick ticks ih =>
    cases recording with
    | cons actual rest =>
      obtain ⟨middle, initial, final, initialSafe, finalSafe⟩ := ih rest safe.2
      exact ⟨middle, .cons actual initial, final, ⟨safe.1, initialSafe⟩, finalSafe⟩

end LeanCage.Host.Kernel
