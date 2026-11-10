import FilesystemSourceIntervals

namespace LeanCage.Host.Kernel
open Filesystem

variable {sourceProgram : Program UInt32}

-- §FS-host-boundary.ownership: Select an actual earlier row of the constructed ownership
-- journal, retaining both source intervals and the exact intermediate family labels.
structure OwnershipCut {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram)
    {all : List (ActorTick runtime)} (catalogue : Catalogue runtime all)
    (before : Population) (first : Family) (ticks : List (ActorTick runtime))
    (after : Population) (final : Family) (position : Nat) (tick : ActorTick runtime) where
  leading : List (ActorTick runtime)
  trailing : List (ActorTick runtime)
  beforeFamily : Family
  afterFamily : Family
  trace : ticks = leading ++ tick :: trailing
  count : leading.length = position
  initial : OwnershipJournal runtime catalogue before first leading tick.before beforeFamily
  current : CustodyOwnershipStep catalogue tick beforeFamily afterFamily
  remaining : OwnershipJournal runtime catalogue tick.after afterFamily trailing after final

theorem OwnershipJournal.selected_cut {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {all : List (ActorTick runtime)} {catalogue : Catalogue runtime all}
    {before after : Population} {first final : Family} {ticks : List (ActorTick runtime)}
    (journal : OwnershipJournal runtime catalogue before first ticks after final)
    {position : Nat} {tick : ActorTick runtime} (selected : ticks[position]? = some tick) :
    Nonempty (OwnershipCut runtime catalogue before first ticks after final position tick) := by
  induction journal generalizing position with
  | nil population family => cases position <;> simp at selected
  | @cons head tail after first middle final step rest ih =>
    cases position with
    | zero =>
      have same : head = tick := by simpa only [List.getElem?_cons_zero, Option.some.injEq] using selected
      subst tick
      exact ⟨⟨[], tail, first, middle, rfl, rfl, .nil _ _, step, rest⟩⟩
    | succ position =>
      have selected : tail[position]? = some tick := by simpa only [List.getElem?_cons_succ] using selected
      obtain ⟨cut⟩ := ih selected
      exact ⟨{
        leading := head :: cut.leading
        trailing := cut.trailing
        beforeFamily := cut.beforeFamily
        afterFamily := cut.afterFamily
        trace := by simp only [cut.trace, List.cons_append]
        count := by simp only [List.length_cons, cut.count]
        initial := .cons step cut.initial
        current := cut.current
        remaining := cut.remaining }⟩

-- §FS-host-boundary.ownership: Ownership uniqueness is independent of when allocation was
-- observed. A catalogue validated later may contain births after this selected source cut.
theorem OwnershipJournal.private_binding_retained_unique {kernel : Contract}
    {runtime : ActorRuntime kernel sourceProgram}
    (lifetimes : LifetimeContract runtime) {all : List (ActorTick runtime)} {catalogue : Catalogue runtime all}
    {before after : Population} {first final : Family} {ticks : List (ActorTick runtime)}
    (journal : OwnershipJournal runtime catalogue before first ticks after final)
    {actor : ActorId} {parent object scope : ObjectId} {name : ByteArray}
    (unique : ∀ other, catalogue.Owns other scope → other = actor)
    (allocated : before.shared.allocated object = true) (privateObject : first object = some scope)
    (bound : before.shared.entries parent name = some object)
    (quiet : ∀ tick ∈ ticks, ∀ request observed,
      tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)) → ¬ DestructiveRequest request) :
    after.shared.entries parent name = some object ∧ final object = some scope := by
  have cannotMutate : ∀ tick ∈ ticks, ¬ OwnerMutation catalogue tick scope := by
    intro tick member mutation
    obtain ⟨other, request, observed, selected, destructive, owned⟩ := mutation
    have same := unique other owned
    subst other
    exact quiet tick member request observed selected destructive
  induction journal with
  | nil => exact ⟨bound, privateObject⟩
  | @cons tick ticks after first middle final step tail ih =>
    have retainedBinding : tick.after.shared.entries parent name = some object := by
      by_cases kept : tick.after.shared.entries parent name = some object
      · exact kept
      · exact False.elim (cannotMutate tick (by simp) (step.removed parent name object scope bound privateObject kept))
    have retainedLabel : middle object = some scope := by
      by_cases kept : middle object = some scope
      · exact kept
      · exact False.elim (cannotMutate tick (by simp) (step.released object scope allocated privateObject kept))
    exact ih (actor_step_allocated lifetimes tick.operation object allocated) retainedLabel retainedBinding
      (by intro tick member request observed selected; exact quiet tick (by simp [member]) request observed selected)
      (by intro tick member; exact cannotMutate tick (by simp [member]))

theorem OwnershipJournal.private_binding_retained_catalogued {kernel : Contract}
    {runtime : ActorRuntime kernel sourceProgram}
    (lifetimes : LifetimeContract runtime) {all : List (ActorTick runtime)} {catalogue : Catalogue runtime all}
    {before after : Population} {first final : Family} {ticks : List (ActorTick runtime)}
    (journal : OwnershipJournal runtime catalogue before first ticks after final)
    {observedWorld : World} (valid : catalogue.Valid observedWorld)
    {actor : ActorId} {parent object scope : ObjectId} {name : ByteArray}
    (owner : catalogue.Owns actor scope) (allocated : before.shared.allocated object = true)
    (privateObject : first object = some scope) (bound : before.shared.entries parent name = some object)
    (quiet : ∀ tick ∈ ticks, ∀ request observed,
      tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)) → ¬ DestructiveRequest request) :
    after.shared.entries parent name = some object ∧ final object = some scope :=
  journal.private_binding_retained_unique lifetimes
    (fun _other owned => catalogue_unique_owner valid owned owner) allocated privateObject bound quiet

end LeanCage.Host.Kernel
