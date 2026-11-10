import FilesystemFamilyJournal
import FilesystemLookupNames

namespace LeanCage.Host.Kernel

-- §FS-host-boundary.ownership: These are application label updates, not allowed kernel effects.
-- Actual source/native transitions separately establish the next physical custody state.
inductive FamilyUpdate (before : World) (first : Family) : Family → Prop where
  | same : FamilyUpdate before first first
  | fresh (object scope : ObjectId) (absent : before.allocated object = false) :
      FamilyUpdate before first (setFamily first object scope)
  | published (scope : ObjectId) : FamilyUpdate before first (clearFamily first scope)

def EqualExistingLabels (world : World) (first final : Family) : Prop :=
  ∀ left right, world.allocated left = true → world.allocated right = true →
    first left = first right → final left = final right

theorem FamilyUpdate.existing {before after : World} {first final : Family}
    (update : FamilyUpdate before first final) : ExistingLabels before after first final := by
  cases update with
  | same => exact unchanged_existing_labels _ _ _
  | fresh object scope absent => exact set_family_existing_labels absent
  | published scope => exact clear_family_existing_labels _ _ _ _

theorem FamilyUpdate.equal {world : World} {first final : Family}
    (update : FamilyUpdate world first final) : EqualExistingLabels world first final := by
  intro left right leftAllocated rightAllocated equal
  cases update with
  | same => exact equal
  | fresh object scope absent =>
    have leftDifferent : left ≠ object := by intro same; rw [same, absent] at leftAllocated; cases leftAllocated
    have rightDifferent : right ≠ object := by intro same; rw [same, absent] at rightAllocated; cases rightAllocated
    simpa only [setFamily, ite_eq_right leftDifferent, ite_eq_right rightDifferent] using equal
  | published scope => simp only [clearFamily, equal]

theorem equal_existing_trans {first middle : World} {before between after : Family}
    (initial : EqualExistingLabels first before between) (final : EqualExistingLabels middle between after)
    (allocation : ∀ object, first.allocated object = true → middle.allocated object = true) :
    EqualExistingLabels first before after := by
  intro left right leftAllocated rightAllocated equal
  exact final left right (allocation left leftAllocated) (allocation right rightAllocated)
    (initial left right leftAllocated rightAllocated equal)

variable {sourceProgram : Program UInt32}

-- §FS-host-boundary.ownership: The completed induction prefix retains current lookup facts
-- and exact application scope updates. It is constructed alongside the physical custody fold.
inductive ScopeJournal {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram)
    (initialObjects : ObjectId → Bool) (dataObjects : ObjectId → Prop) (semantics : NameSemanticsView) :
    Population → Family → List (ActorTick runtime) → Population → Family → Prop where
  | nil (population : Population) (family : Family)
      (graph : FamilyGraph population.shared family initialObjects dataObjects)
      (wellFormed : NamespaceWellFormed population.shared)
      (boundaries : ExactPrivateBoundaries semantics population.shared family) :
      ScopeJournal runtime initialObjects dataObjects semantics population family [] population family
  | cons {tick : ActorTick runtime} {ticks : List (ActorTick runtime)}
      {before middle final : Family} {after : Population}
      (graph : FamilyGraph tick.before.shared before initialObjects dataObjects)
      (wellFormed : NamespaceWellFormed tick.before.shared)
      (boundaries : ExactPrivateBoundaries semantics tick.before.shared before)
      (update : FamilyUpdate tick.before.shared before middle)
      (tail : ScopeJournal runtime initialObjects dataObjects semantics tick.after middle ticks after final) :
      ScopeJournal runtime initialObjects dataObjects semantics tick.before before (tick :: ticks) after final

theorem ScopeJournal.family {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {initialObjects : ObjectId → Bool} {dataObjects : ObjectId → Prop} {semantics : NameSemanticsView}
    {before after : Population} {first final : Family} {ticks : List (ActorTick runtime)}
    (journal : ScopeJournal runtime initialObjects dataObjects semantics before first ticks after final) :
    FamilyJournal runtime initialObjects dataObjects before first ticks after final := by
  induction journal with
  | nil population family graph => exact .nil population family graph
  | cons graph wellFormed boundaries update tail ih => exact .cons graph update.existing ih

theorem ScopeJournal.equal {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {initialObjects : ObjectId → Bool} {dataObjects : ObjectId → Prop} {semantics : NameSemanticsView}
    (lifetimes : LifetimeContract runtime)
    {before after : Population} {first final : Family} {ticks : List (ActorTick runtime)}
    (journal : ScopeJournal runtime initialObjects dataObjects semantics before first ticks after final) :
    EqualExistingLabels before.shared first final := by
  induction journal with
  | nil => exact fun _ _ _ _ equal => equal
  | @cons tick ticks first middle final after graph wellFormed boundaries update tail ih =>
    exact equal_existing_trans update.equal ih (fun object => actor_step_allocated lifetimes tick.operation object)

theorem ScopeJournal.selected {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {initialObjects : ObjectId → Bool} {dataObjects : ObjectId → Prop} {semantics : NameSemanticsView}
    {before after : Population} {first final : Family} {ticks : List (ActorTick runtime)}
    (journal : ScopeJournal runtime initialObjects dataObjects semantics before first ticks after final)
    {position : Nat} {tick : ActorTick runtime} (selected : ticks[position]? = some tick) :
    ∃ family rest,
      FamilyGraph tick.before.shared family initialObjects dataObjects ∧
      NamespaceWellFormed tick.before.shared ∧ ExactPrivateBoundaries semantics tick.before.shared family ∧
      ScopeJournal runtime initialObjects dataObjects semantics tick.before family (tick :: rest) after final := by
  induction position generalizing before first ticks with
  | zero =>
    cases journal with
    | nil => cases selected
    | @cons current ticks first middle final after graph wellFormed boundaries update tail =>
      have same : current = tick := Option.some.inj selected
      subst current
      exact ⟨first, ticks, graph, wellFormed, boundaries, .cons graph wellFormed boundaries update tail⟩
  | succ position ih =>
    cases journal with
    | nil => cases selected
    | cons graph wellFormed boundaries update tail => exact ih tail selected

theorem ScopeJournal.append {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {initialObjects : ObjectId → Bool} {dataObjects : ObjectId → Prop} {semantics : NameSemanticsView}
    {before middle after : Population} {first between final : Family} {leading trailing : List (ActorTick runtime)}
    (initial : ScopeJournal runtime initialObjects dataObjects semantics before first leading middle between)
    (last : ScopeJournal runtime initialObjects dataObjects semantics middle between trailing after final) :
    ScopeJournal runtime initialObjects dataObjects semantics before first (leading ++ trailing) after final := by
  induction initial with
  | nil => exact last
  | cons graph wellFormed boundaries update tail ih => exact .cons graph wellFormed boundaries update (ih last)

-- §FS-host-boundary.ownership: Extend the completed prefix only with the actual next tick
-- and its separately established physical state and source-owned label update.
theorem ScopeJournal.extend {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {initialObjects : ObjectId → Bool} {dataObjects : ObjectId → Prop} {semantics : NameSemanticsView}
    {initial : Population} {first before after : Family} {leading : List (ActorTick runtime)}
    {tick : ActorTick runtime}
    (history : ScopeJournal runtime initialObjects dataObjects semantics initial first leading tick.before before)
    (beforeGraph : FamilyGraph tick.before.shared before initialObjects dataObjects)
    (beforeWellFormed : NamespaceWellFormed tick.before.shared)
    (beforeBoundaries : ExactPrivateBoundaries semantics tick.before.shared before)
    (update : FamilyUpdate tick.before.shared before after)
    (afterGraph : FamilyGraph tick.after.shared after initialObjects dataObjects)
    (afterWellFormed : NamespaceWellFormed tick.after.shared)
    (afterBoundaries : ExactPrivateBoundaries semantics tick.after.shared after) :
    ScopeJournal runtime initialObjects dataObjects semantics initial first (leading ++ [tick]) tick.after after :=
  history.append (.cons beforeGraph beforeWellFormed beforeBoundaries update
    (.nil tick.after after afterGraph afterWellFormed afterBoundaries))

end LeanCage.Host.Kernel
