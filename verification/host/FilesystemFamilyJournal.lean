import FilesystemPublicDirectory
import FilesystemRecording
import FilesystemChanges
import FilesystemLabelFlow

namespace LeanCage.Host.Kernel
open Filesystem

variable {sourceProgram : Program UInt32}

-- §FS-host-boundary.ownership: These are already-proved prefix snapshots used by source inversion.
-- The application fold constructs them; they are not a Linux/runtime primitive assumption.
inductive FamilyJournal {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram)
    (initialObjects : ObjectId → Bool) (dataObjects : ObjectId → Prop) :
    Population → Family → List (ActorTick runtime) → Population → Family → Prop where
  | nil (population : Population) (family : Family)
      (graph : FamilyGraph population.shared family initialObjects dataObjects) :
      FamilyJournal runtime initialObjects dataObjects population family [] population family
  | cons {tick : ActorTick runtime} {ticks : List (ActorTick runtime)}
      {before middle final : Family} {after : Population}
      (graph : FamilyGraph tick.before.shared before initialObjects dataObjects)
      (existing : ExistingLabels tick.before.shared tick.after.shared before middle)
      (tail : FamilyJournal runtime initialObjects dataObjects tick.after middle ticks after final) :
      FamilyJournal runtime initialObjects dataObjects tick.before before (tick :: ticks) after final

theorem family_journal_actor {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {initialObjects : ObjectId → Bool} {dataObjects : ObjectId → Prop}
    {before after : Population} {first final : Family} {ticks : List (ActorTick runtime)}
    (journal : FamilyJournal runtime initialObjects dataObjects before first ticks after final) :
    ActorJournal runtime before ticks after := by
  induction journal with
  | nil => exact .nil _
  | cons graph publicObjects tail ih => exact .cons ih

theorem family_journal_graph {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {initialObjects : ObjectId → Bool} {dataObjects : ObjectId → Prop}
    {before after : Population} {first final : Family} {ticks : List (ActorTick runtime)}
    (journal : FamilyJournal runtime initialObjects dataObjects before first ticks after final) :
    FamilyGraph before.shared first initialObjects dataObjects ∧
      FamilyGraph after.shared final initialObjects dataObjects := by
  induction journal with
  | nil population family graph => exact ⟨graph, graph⟩
  | cons graph publicObjects tail ih => exact ⟨graph, ih.2⟩

-- §FS-host-boundary.ownership: A past public object cannot become a later private birth.
theorem family_journal_public {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {initialObjects : ObjectId → Bool} {dataObjects : ObjectId → Prop}
    (lifetimes : LifetimeContract runtime)
    {before after : Population} {first final : Family} {ticks : List (ActorTick runtime)}
    (journal : FamilyJournal runtime initialObjects dataObjects before first ticks after final)
    {object : ObjectId} (allocated : before.shared.allocated object = true) (publicObject : first object = none) :
    final object = none := by
  induction journal with
  | nil => exact publicObject
  | @cons tick ticks first middle final after graph publicObjects tail ih =>
    exact ih (actor_step_allocated lifetimes tick.operation object allocated)
      (existing_labels_public publicObjects object allocated publicObject)

theorem family_journal_existing {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {initialObjects : ObjectId → Bool} {dataObjects : ObjectId → Prop}
    (lifetimes : LifetimeContract runtime)
    {before after : Population} {first final : Family} {ticks : List (ActorTick runtime)}
    (journal : FamilyJournal runtime initialObjects dataObjects before first ticks after final) :
    ExistingLabels before.shared after.shared first final := by
  induction journal with
  | nil => exact unchanged_existing_labels _ _ _
  | @cons tick ticks first middle final after graph existing tail ih =>
    exact existing_labels_trans existing ih (fun object => actor_step_allocated lifetimes tick.operation object)

theorem family_journal_append {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {initialObjects : ObjectId → Bool} {dataObjects : ObjectId → Prop}
    {before middle after : Population} {first between final : Family} {leading trailing : List (ActorTick runtime)}
    (initial : FamilyJournal runtime initialObjects dataObjects before first leading middle between)
    (last : FamilyJournal runtime initialObjects dataObjects middle between trailing after final) :
    FamilyJournal runtime initialObjects dataObjects before first (leading ++ trailing) after final := by
  induction initial with
  | nil => exact last
  | cons graph existing tail ih => exact .cons graph existing (ih last)

theorem family_journal_selected_suffix {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {initialObjects : ObjectId → Bool} {dataObjects : ObjectId → Prop}
    {before after : Population} {first final : Family} {ticks : List (ActorTick runtime)}
    (journal : FamilyJournal runtime initialObjects dataObjects before first ticks after final)
    {position : Nat} {tick : ActorTick runtime} (selected : ticks[position]? = some tick) :
    ∃ family rest, FamilyGraph tick.before.shared family initialObjects dataObjects ∧
      FamilyJournal runtime initialObjects dataObjects tick.before family (tick :: rest) after final := by
  induction position generalizing before first ticks with
  | zero =>
    cases journal with
    | nil => cases selected
    | @cons current ticks first middle final after graph publicObjects tail =>
      have same : current = tick := Option.some.inj selected
      subst current
      exact ⟨first, ticks, graph, .cons graph publicObjects tail⟩
  | succ position ih =>
    cases journal with
    | nil => cases selected
    | cons graph publicObjects tail => exact ih tail selected

-- §FS-host-boundary.acceptance: Restrict an actual phase recording to its genuine source ordinals.
theorem recorded_history_source_bound {kernel : Contract} {origin : FilesystemOrigin} {ordinal : Nat}
    {before after : World} {events : List (Request × Reply)}
    (history : RecordedHistory kernel origin ordinal before events after) (limit : Nat)
    (bound : ordinal + events.length ≤ limit) :
    RecordedHistory kernel (fun index request reply before after =>
      origin index request reply before after ∧ index < limit) ordinal before events after := by
  induction history with
  | nil => exact .nil _ _
  | cons actual sampled tail ih =>
    apply RecordedHistory.cons actual
    · exact ⟨sampled, by simp only [List.length_cons] at bound; omega⟩
    · apply ih
      simp only [List.length_cons] at bound
      omega
  | environment actual tail ih => exact .environment actual (ih bound)

end LeanCage.Host.Kernel
