import GatewayWriterReturnedExecution

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {ticks : List (ActorTick runtime)} {pair : Pair} {Token : Type}

theorem ObservedStep.engine_commit_cursor
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {initialWorld : World} {population : Population}
    (source : ActorJournal runtime (Population.empty initialWorld) ticks population)
    {position : Nat} {tick : ActorTick runtime} (selectedTick : ticks[position]? = some tick)
    {first last : PhysicalState} {record : Record} (step : ObservedStep primitive first record last)
    (atPosition : record.position = position) (registered : Registered primitive position first)
    (aligned : ReturnedSourceAligned tick.before first.ledger)
    (actor ordinal extent : Nat) (event : record.event = .commit (.engine actor ordinal) extent) :
    ∃ engine, tick.before.actors actor = some engine ∧ ordinal = returnedOrdinal engine.events := by
  cases step with
  | engine | native | read | birth | other => cases event
  | observation position inside token current state initial final reply selected live actual =>
    cases reply <;> cases event
  | commit actualPosition inside token current state initial final extent selected live actual =>
    simp only at atPosition
    subst actualPosition
    have key := (ProgressEvent.commit.inj event).1
    exact actual_engine_commit_cursor source selectedTick _ registered aligned token current initial final extent
      selected actual actor ordinal key

theorem PendingBatch.engine_commit_cursors
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {initialWorld : World} {population : Population}
    (source : ActorJournal runtime (Population.empty initialWorld) ticks population)
    {position : Nat} {tick : ActorTick runtime} (selectedTick : ticks[position]? = some tick)
    {initial final : PhysicalState} {records : List Record}
    (batch : PendingBatch primitive position initial final records)
    (registered : Registered primitive position initial)
    (aligned : ReturnedSourceAligned tick.before initial.ledger) :
    ∀ record ∈ records, ∀ actor ordinal extent, record.event = .commit (.engine actor ordinal) extent →
      ∃ engine, tick.before.actors actor = some engine ∧ ordinal = returnedOrdinal engine.events := by
  obtain ⟨actual, positions, unobserved⟩ := batch
  induction actual with
  | nil => simp
  | @cons start initial middle final head rest order step tail ih =>
    have headPosition := positions head (by simp)
    have initialAt : Registered primitive head.position initial := registered.later order
    have fixed : head.position = start := headPosition
    have beforeHead : Registered primitive start initial := by simpa only [fixed] using initialAt
    have one : PendingBatch primitive start initial middle [head] := {
      actual := .cons (by omega) step (.nil _ _)
      positions := by intro item member; cases List.mem_singleton.mp member; exact headPosition
      unobserved := by intro item member; cases List.mem_singleton.mp member; exact unobserved head (by simp) }
    have middleRegistered : Registered primitive start middle := by
      simpa only [fixed] using step.registered order registered
    have middleAligned := aligned.pending selectedTick one
    intro record member actor ordinal extent event
    rcases List.mem_cons.mp member with same | later
    · subst record
      exact step.engine_commit_cursor source selectedTick headPosition beforeHead aligned actor ordinal extent event
    · exact ih (by simpa only [headPosition] using selectedTick)
        (by simpa only [headPosition] using middleRegistered) middleAligned
        (fun item member => (positions item (by simp [member])).trans headPosition.symm)
        (fun item member => unobserved item (by simp [member])) record later actor ordinal extent event

theorem EngineRow.no_commit
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {position : Nat} {tick : ActorTick runtime} {initial final : PhysicalState} {records : List Record}
    (row : EngineRow primitive position tick initial records final) :
    ∀ record ∈ records, ∀ key extent, record.event ≠ .commit key extent := by
  cases row with
  | absent | outside => simp
  | acknowledged entry reply actual atPosition sameTick =>
    intro record member key extent
    cases List.mem_singleton.mp member
    cases reply <;> simp [observationEvent]

-- §FS-host-boundary.caller: Every partial engine write carries the actual
-- actor's returned-call cursor at its own global row, including after loss.
theorem SynchronizedJournal.engine_commit_cursors
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {initialWorld : World} {population : Population}
    (source : ActorJournal runtime (Population.empty initialWorld) ticks population)
    {position : Nat} {remaining : List (ActorTick runtime)}
    {initial final : PhysicalState} {records : List Record}
    (physical : SynchronizedJournal primitive position remaining initial records final)
    {first last : Population} (actors : ActorJournal runtime first remaining last)
    (registered : Registered primitive position initial) (aligned : ReturnedSourceAligned first initial.ledger) :
    ∀ record ∈ records, ∀ actor ordinal extent, record.event = .commit (.engine actor ordinal) extent →
      ∃ tick engine, ticks[record.position]? = some tick ∧ tick.before.actors actor = some engine ∧
        ordinal = returnedOrdinal engine.events := by
  induction physical generalizing first with
  | nil => simp
  | @cons position tick remaining initial pending acknowledged final progress replies rest selected batch row tail ih =>
    cases actors with
    | cons actorTail =>
      have atPending : Registered primitive position pending := batch.actual.registered_at registered (Nat.le_refl _)
        (fun record member => by rw [batch.positions record member]; exact Nat.le_refl _)
      have afterPending := aligned.pending selected batch
      have afterRow := afterPending.advance source selected row atPending
      have nextRegistered : Registered primitive (position + 1) acknowledged :=
        (row.run.registered_at atPending (Nat.le_refl _)
          (fun record member => by rw [row.positions record member]; exact Nat.le_refl _)).later (by omega)
      intro record member actor ordinal extent event
      rcases List.mem_append.mp member with head | later
      · rcases List.mem_append.mp head with head | reply
        · obtain ⟨engine, present, cursor⟩ := batch.engine_commit_cursors source selected registered aligned
            record head actor ordinal extent event
          exact ⟨tick, engine, by rw [batch.positions record head]; exact selected, present, cursor⟩
        · exact False.elim (row.no_commit record reply _ _ event)
      · exact ih actorTail nextRegistered afterRow record later actor ordinal extent event

theorem ObservedJournal.position_lower_bound
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {position : Nat} {initial final : PhysicalState} {records : List Record}
    (journal : ObservedJournal primitive position initial records final) :
    ∀ record ∈ records, position ≤ record.position := by
  induction journal with
  | nil => simp
  | cons ordered actual tail ih =>
    intro record member
    rcases List.mem_cons.mp member with same | member
    · subst record; exact ordered
    · exact Nat.le_trans ordered (ih record member)

theorem ObservedJournal.positions_ordered
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {position : Nat} {initial final : PhysicalState} {records : List Record}
    (journal : ObservedJournal primitive position initial records final) :
    records.Pairwise (fun first last => first.position ≤ last.position) := by
  induction journal with
  | nil => exact .nil
  | cons ordered actual tail ih => exact .cons tail.position_lower_bound ih

-- §FS-host-boundary.caller: Projecting a single engine's commits preserves
-- source ordinal order. An ACK cannot be bypassed to enqueue an older chunk.
theorem actual_engine_commits_ordered
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {initialWorld : World} {population : Population}
    (source : ActorJournal runtime (Population.empty initialWorld) ticks population)
    {final : PhysicalState} {records : List Record}
    (physical : SynchronizedJournal primitive 0 ticks .unborn records final) (actor : ActorId) :
    records.Pairwise (fun first last => ∀ firstOrdinal lastOrdinal firstExtent lastExtent,
      first.event = .commit (.engine actor firstOrdinal) firstExtent →
      last.event = .commit (.engine actor lastOrdinal) lastExtent → firstOrdinal ≤ lastOrdinal) := by
  have cursors := physical.engine_commit_cursors source source (registered_unborn primitive) (by
    intro actor engine absent; cases absent)
  apply List.pairwise_iff_getElem.mpr
  intro first last firstInside lastInside order
  have positions := List.pairwise_iff_getElem.mp physical.erase.positions_ordered first last firstInside lastInside order
  intro firstOrdinal lastOrdinal firstExtent lastExtent firstEvent lastEvent
  obtain ⟨firstTick, firstEngine, firstSelected, firstPresent, firstCursor⟩ :=
    cursors _ (List.getElem_mem firstInside) actor firstOrdinal firstExtent firstEvent
  obtain ⟨lastTick, lastEngine, lastSelected, lastPresent, lastCursor⟩ :=
    cursors _ (List.getElem_mem lastInside) actor lastOrdinal lastExtent lastEvent
  rw [firstCursor, lastCursor]
  exact actual_engine_commit_cursors_ordered source firstSelected lastSelected positions actor
    firstEngine lastEngine firstPresent lastPresent

end LeanCage.Host.PrivateStreams
