import FilesystemProjection

namespace LeanCage.Host.Kernel
open Filesystem

variable {sourceProgram : Program UInt32}

-- §FS-host-boundary.acceptance: Retain the exact global tick and the actor's source-event ordinal.
def SourceReturnAt {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram) (ticks : List (ActorTick runtime))
    (actor : ActorId) : OperationOrigin :=
  fun ordinal _ effect reply before after => ∃ (position : Nat) (tick : ActorTick runtime) (initial final : EngineState),
    ticks[position]? = some tick ∧ tick.action = .returned actor effect reply ∧
    tick.before.actors actor = some initial ∧ tick.after.actors actor = some final ∧
    initial.events.length = ordinal ∧ before = tick.before.project initial ∧ after = tick.after.project final

theorem journal_captures_source {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (actor : ActorId) (all : List (ActorTick runtime)) {ticks : List (ActorTick runtime)}
    (included : ∀ tick ∈ ticks, tick ∈ all) : Captures runtime actor (SourceReturnAt runtime all actor) ticks := by
  intro tick member β effect reply initial final action beforePresent afterPresent
  obtain ⟨position, bound, actual⟩ := List.mem_iff_getElem.mp (included tick member)
  exact ⟨position, tick, initial, final,
    List.getElem?_eq_some_iff.mpr ⟨bound, actual⟩, action, beforePresent, afterPresent, rfl, rfl, rfl⟩

-- §FS-host-boundary.acceptance: No physical event is detached from the journal during projection.
theorem actor_journal_recorded_projection {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (environment : InterferenceContract kernel)
    (all : List (ActorTick runtime)) {before after : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime before ticks after) (included : ∀ tick ∈ ticks, tick ∈ all)
    (valid : before.Consistent) (actor : ActorId) (initial final : EngineState)
    (initialPresent : before.actors actor = some initial) (initialLive : initial.running = true)
    (finalPresent : after.actors actor = some final) (finalLive : final.running = true) :
    ∃ events, final.events = initial.events ++ events ∧ Residual initial.current events final.current ∧
      ActorHistoryWith runtime actor (SourceReturnAt runtime all actor) initial.events.length
        (before.project initial) events (after.project final) :=
  actor_journal_projection_with (projection_from_reference_laws descriptors lifetimes references environment)
    journal (actor_journal_consistent descriptors lifetimes references journal valid).2
    actor (SourceReturnAt runtime all actor) (journal_captures_source actor all included)
    initial final initialPresent initialLive finalPresent finalLive

theorem actor_with_append {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram} {actor : ActorId}
    {origin : OperationOrigin} {ordinal : Nat} {before middle after : World} {first last : List Program.Event}
    (initial : ActorHistoryWith runtime actor origin ordinal before first middle)
    (final : ActorHistoryWith runtime actor origin (ordinal + first.length) middle last after) :
    ActorHistoryWith runtime actor origin ordinal before (first ++ last) after := by
  induction initial with
  | nil => exact final
  | returned actual recorded tail ih =>
    apply ActorHistoryWith.returned actual recorded
    apply ih
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using final
  | environment interference tail ih => exact .environment interference (ih final)

theorem actor_with_head {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram} {actor : ActorId}
    {origin : OperationOrigin} {ordinal : Nat} {β : Type} {effect : Effect β} {reply : β}
    {before after : World} {events : List Program.Event}
    (history : ActorHistoryWith runtime actor origin ordinal before (.returned effect reply :: events) after) :
    ∃ actual middle, ActorHistoryWith runtime actor origin ordinal before [] actual ∧
      ActorOperation runtime actor effect (some reply) actual middle ∧ origin ordinal β effect reply actual middle ∧
      ActorHistoryWith runtime actor origin (ordinal + 1) middle events after := by
  generalize shape : .returned effect reply :: events = all at history
  induction history with
  | nil => cases shape
  | returned actual recorded tail ih => cases shape; exact ⟨_, _, .nil _ _, actual, recorded, tail⟩
  | environment interference tail ih =>
    obtain ⟨actual, middle, initial, operation, recorded, rest⟩ := ih shape
    exact ⟨actual, middle, .environment interference initial, operation, recorded, rest⟩

private theorem actor_with_no_lost {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram} {actor : ActorId}
    {origin : OperationOrigin} {ordinal : Nat} {β : Type} {effect : Effect β}
    {before after : World} {events : List Program.Event} :
    ¬ ActorHistoryWith runtime actor origin ordinal before (.lost effect :: events) after := by
  intro history
  generalize shape : .lost effect :: events = all at history
  induction history with
  | nil => cases shape
  | returned actual recorded tail ih => cases shape
  | environment interference tail ih => exact ih shape

theorem actor_with_split {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram} {actor : ActorId}
    {origin : OperationOrigin} {ordinal : Nat} {before after : World} (first last : List Program.Event)
    (history : ActorHistoryWith runtime actor origin ordinal before (first ++ last) after) :
    ∃ middle, ActorHistoryWith runtime actor origin ordinal before first middle ∧
      ActorHistoryWith runtime actor origin (ordinal + first.length) middle last after := by
  induction first generalizing before ordinal with
  | nil => exact ⟨before, .nil _ _, history⟩
  | cons event rest ih =>
    cases event with
    | lost effect => exact False.elim (actor_with_no_lost history)
    | returned effect reply =>
      obtain ⟨actual, between, leading, operation, recorded, tail⟩ := actor_with_head history
      obtain ⟨middle, initial, final⟩ := ih tail
      refine ⟨middle, actor_with_append leading (.returned operation recorded initial), ?_⟩
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using final

abbrev FilesystemOrigin := Nat → Request → Reply → World → World → Prop

inductive RecordedHistory (kernel : Contract) (origin : FilesystemOrigin) :
    Nat → World → List (Request × Reply) → World → Prop where
  | nil (ordinal : Nat) (world : World) : RecordedHistory kernel origin ordinal world [] world
  | cons {ordinal : Nat} {before middle after : World} {request : Request} {reply : Reply}
      {events : List (Request × Reply)} (actual : kernel.step before request (some reply) middle)
      (recorded : origin ordinal request reply before middle)
      (tail : RecordedHistory kernel origin (ordinal + 1) middle events after) :
      RecordedHistory kernel origin ordinal before ((request, reply) :: events) after
  | environment {ordinal : Nat} {before middle after : World} {events : List (Request × Reply)}
      (interference : kernel.interference before middle) (tail : RecordedHistory kernel origin ordinal middle events after) :
      RecordedHistory kernel origin ordinal before events after

theorem recorded_history_erase {kernel : Contract} {origin : FilesystemOrigin} {ordinal : Nat}
    {before after : World} {events : List (Request × Reply)}
    (history : RecordedHistory kernel origin ordinal before events after) : History kernel before events after := by
  induction history with
  | nil => exact .nil _
  | cons actual recorded tail ih => exact .cons actual ih
  | environment interference tail ih => exact .environment interference ih

theorem actor_recorded_filesystem {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram} {actor : ActorId}
    {origin : OperationOrigin} {ordinal : Nat} {before after : World} {events : List (Request × Reply)}
    (history : ActorHistoryWith runtime actor origin ordinal before (events.map Program.filesystemEvent) after) :
    RecordedHistory kernel (fun ordinal request reply => origin ordinal Reply (.filesystem request) reply)
      ordinal before events after := by
  generalize shape : events.map Program.filesystemEvent = all at history
  induction history generalizing events with
  | nil => cases events <;> cases shape; exact .nil _ _
  | returned actual recorded tail ih =>
    cases events with
    | nil => cases shape
    | cons event rest =>
      cases event with
      | mk request reply => cases shape; exact .cons actual recorded (ih rfl)
  | environment interference tail ih => exact .environment interference (ih shape)

theorem recorded_history_head {kernel : Contract} {origin : FilesystemOrigin} {ordinal : Nat}
    {before after : World} {request : Request} {reply : Reply} {events : List (Request × Reply)}
    (history : RecordedHistory kernel origin ordinal before ((request, reply) :: events) after) :
    ∃ actual middle, RecordedHistory kernel origin ordinal before [] actual ∧
      kernel.step actual request (some reply) middle ∧ origin ordinal request reply actual middle ∧
      RecordedHistory kernel origin (ordinal + 1) middle events after := by
  generalize shape : (request, reply) :: events = all at history
  induction history with
  | nil => cases shape
  | cons actual recorded tail ih => cases shape; exact ⟨_, _, .nil _ _, actual, recorded, tail⟩
  | environment interference tail ih =>
    obtain ⟨actual, middle, leading, operation, recorded, rest⟩ := ih shape
    exact ⟨actual, middle, .environment interference leading, operation, recorded, rest⟩

theorem recorded_history_append {kernel : Contract} {origin : FilesystemOrigin} {ordinal : Nat}
    {before middle after : World} {first last : List (Request × Reply)}
    (initial : RecordedHistory kernel origin ordinal before first middle)
    (final : RecordedHistory kernel origin (ordinal + first.length) middle last after) :
    RecordedHistory kernel origin ordinal before (first ++ last) after := by
  induction initial with
  | nil => exact final
  | cons actual recorded tail ih =>
    apply RecordedHistory.cons actual recorded
    apply ih
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using final
  | environment interference tail ih => exact .environment interference (ih final)

theorem recorded_history_split {kernel : Contract} {origin : FilesystemOrigin} {ordinal : Nat}
    {before after : World} (first last : List (Request × Reply))
    (history : RecordedHistory kernel origin ordinal before (first ++ last) after) :
    ∃ middle, RecordedHistory kernel origin ordinal before first middle ∧
      RecordedHistory kernel origin (ordinal + first.length) middle last after := by
  induction first generalizing before ordinal with
  | nil => exact ⟨before, .nil _ _, history⟩
  | cons event rest ih =>
    obtain ⟨actual, between, leading, operation, recorded, tail⟩ := recorded_history_head history
    obtain ⟨middle, initial, final⟩ := ih tail
    refine ⟨middle, recorded_history_append leading (.cons operation recorded initial), ?_⟩
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using final

def RecordedRun (kernel : Contract) (origin : FilesystemOrigin) (ordinal : Nat) {α : Type}
    (program : Filesystem.Program α) (before : World) (events : List (Request × Reply))
    (after : World) (value : α) : Prop :=
  Returns program events value ∧ RecordedHistory kernel origin ordinal before events after

theorem recorded_run_bind_split {kernel : Contract} {origin : FilesystemOrigin} {ordinal : Nat} {α β : Type}
    (program : Filesystem.Program α) (next : α → Filesystem.Program β)
    {before after : World} {events : List (Request × Reply)} {result : β}
    (run : RecordedRun kernel origin ordinal (program.bind next) before events after result) :
    ∃ first value last middle,
      events = first ++ last ∧ RecordedRun kernel origin ordinal program before first middle value ∧
      RecordedRun kernel origin (ordinal + first.length) (next value) middle last after result := by
  obtain ⟨first, value, last, initial, final, shape⟩ := Snapshot.returns_bind_split _ _ run.1
  have history := run.2
  rw [shape] at history
  obtain ⟨middle, leading, rest⟩ := recorded_history_split first last history
  exact ⟨first, value, last, middle, shape, ⟨initial, leading⟩, ⟨final, rest⟩⟩

theorem recorded_filesystem_phase {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram} {actor : ActorId}
    {origin : OperationOrigin} {ordinal : Nat} {α : Type} {program : Filesystem.Program α}
    {before after : World} {context tail : List Program.Event} {events : List (Request × Reply)} {value : α}
    (history : ActorHistoryWith runtime actor origin ordinal before
      (context ++ events.map Program.filesystemEvent ++ tail) after) (source : Returns program events value) :
    ∃ first last, ActorHistoryWith runtime actor origin ordinal before context first ∧
      Returns program events value ∧
      RecordedHistory kernel (fun index request reply => origin index Reply (.filesystem request) reply)
        (ordinal + context.length) first events last ∧
      ActorHistoryWith runtime actor origin (ordinal + context.length + events.length) last tail after := by
  rw [List.append_assoc] at history
  obtain ⟨first, leading, rest⟩ := actor_with_split context _ history
  obtain ⟨last, phase, final⟩ := actor_with_split (events.map Program.filesystemEvent) tail rest
  exact ⟨first, last, leading, source, actor_recorded_filesystem phase, by simpa only [List.length_map] using final⟩

theorem selected_tick_split {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {ticks : List (ActorTick runtime)} {position : Nat} {tick : ActorTick runtime}
    (selected : ticks[position]? = some tick) :
    ∃ leading trailing, ticks = leading ++ tick :: trailing := by
  induction position generalizing ticks with
  | zero =>
    cases ticks with
    | nil => cases selected
    | cons first rest =>
      have same : first = tick := Option.some.inj selected
      subst first
      exact ⟨[], rest, rfl⟩
  | succ position ih =>
    cases ticks with
    | nil => cases selected
    | cons first rest =>
      obtain ⟨leading, trailing, shape⟩ := ih selected
      exact ⟨first :: leading, trailing, by rw [shape]; rfl⟩

def ActorAction.eventFor (action : ActorAction) (actor : ActorId) : Option Program.Event :=
  match action with
  | .returned owner effect reply => if actor = owner then some (.returned effect reply) else none
  | .lost owner effect => if actor = owner then some (.lost effect) else none
  | _ => none

-- §FS-host-boundary.acceptance: The same selected call's complete input prefix includes
-- failure/loss.
theorem selected_source_prefix_for {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState} {event : Program.Event}
    (selected : ticks[position]? = some tick) (action : tick.action.eventFor actor = some event)
    (present : tick.before.actors actor = some engine) :
    Program.Prefix sourceProgram (engine.events ++ [event]) := by
  obtain ⟨leading, trailing, shape⟩ := selected_tick_split selected
  have source := actor_journal_selected_source_for journal leading trailing tick shape actor engine present
  rcases tick with ⟨kind, population, afterPopulation, operation⟩
  cases operation with
  | launch => cases action
  | @returned β population owner current effect next reply world currentPresent alive head actual =>
    dsimp only [ActorAction.eventFor] at action
    split at action
    · rename_i sameActor
      subst owner
      cases action
      have same := Option.some.inj (present.symm.trans currentPresent)
      subst engine
      have reached : Residual sourceProgram current.events current.current := by
        simpa only [EngineSourceFrom, alive, Bool.true_eq, ite_true] using source
      apply residual_prefix reached
      rw [head]
      exact .returned _ _ _ [] (.empty _)
    · cases action
  | @lost β population owner current effect next world currentPresent alive head actual =>
    dsimp only [ActorAction.eventFor] at action
    split at action
    · rename_i sameActor
      subst owner
      cases action
      have same := Option.some.inj (present.symm.trans currentPresent)
      subst engine
      have reached : Residual sourceProgram current.events current.current := by
        simpa only [EngineSourceFrom, alive, Bool.true_eq, ite_true] using source
      apply residual_prefix reached
      rw [head]
      exact .lost _ _
    · cases action
  | foreign | retire | nativeRetire => cases action

theorem selected_source_prefix {kernel : Contract} {runtime : ActorRuntime kernel}
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState} {event : Program.Event}
    (selected : ticks[position]? = some tick) (action : tick.action.eventFor actor = some event)
    (present : tick.before.actors actor = some engine) :
    Program.Prefix Entrypoint.run (engine.events ++ [event]) :=
  selected_source_prefix_for journal selected action present

theorem actor_step_event_prefix {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {action : ActorAction} {before after : Population} (step : ActorStep runtime action before after)
    (query : ActorId) (initial : EngineState) (present : before.actors query = some initial) :
    ∃ final extra, after.actors query = some final ∧ final.events = initial.events ++ extra := by
  cases step with
  | @launch population actor references closeExec workingDirectory fresh absent inherited =>
    have different : query ≠ actor := by intro same; subst query; rw [absent] at present; cases present
    exact ⟨initial, [], by simpa only [Population.launch, Population.install, ite_eq_right different] using present,
      by simp⟩
  | @returned β population actor engine effect next reply world current alive head actual =>
    by_cases same : query = actor
    · subst actor
      have sameEngine := Option.some.inj (present.symm.trans current)
      subst engine
      refine ⟨initial.returned effect reply next world, [.returned effect reply], ?_, rfl⟩
      simp [Population.advance, Population.install]
    · exact ⟨initial, [], by simpa only [Population.advance, Population.install, ite_eq_right same] using present,
        by simp⟩
  | @lost β population actor engine effect next world current alive head actual =>
    by_cases same : query = actor
    · subst actor
      have sameEngine := Option.some.inj (present.symm.trans current)
      subst engine
      refine ⟨initial.lost effect world, [.lost effect], ?_, rfl⟩
      simp [Population.advance, Population.install]
    · exact ⟨initial, [], by simpa only [Population.advance, Population.install, ite_eq_right same] using present,
        by simp⟩
  | foreign actual => exact ⟨initial, [], present, by simp⟩
  | @retire population actor engine observation world current actual =>
    by_cases same : query = actor
    · subst actor
      have identity := Option.some.inj (present.symm.trans current)
      subst engine
      exact ⟨initial.retired observation world, [], by simp [Population.advance, Population.install], by simp [EngineState.retired]⟩
    · exact ⟨initial, [], by simpa only [Population.advance, Population.install, ite_eq_right same] using present,
        by simp⟩
  | nativeRetire actual => exact ⟨initial, [], present, by simp⟩

theorem actor_journal_event_prefix {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {before after : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime before ticks after) (actor : ActorId) (initial final : EngineState)
    (initialPresent : before.actors actor = some initial) (finalPresent : after.actors actor = some final) :
    ∃ extra, final.events = initial.events ++ extra := by
  induction journal generalizing initial with
  | nil =>
    have same := Option.some.inj (initialPresent.symm.trans finalPresent)
    subst initial
    exact ⟨[], by simp⟩
  | @cons tick ticks after tail ih =>
    obtain ⟨middle, first, middlePresent, firstShape⟩ := actor_step_event_prefix tick.operation actor initial initialPresent
    obtain ⟨last, lastShape⟩ := ih middle middlePresent finalPresent
    exact ⟨first ++ last, by rw [lastShape, firstShape, List.append_assoc]⟩

theorem journal_to_selected {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {before after : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime before ticks after) {position : Nat} {tick : ActorTick runtime}
    (selected : ticks[position]? = some tick) : ∃ leading, ActorJournal runtime before leading tick.before := by
  obtain ⟨leading, trailing, shape⟩ := selected_tick_split selected
  rw [shape] at journal
  obtain ⟨middle, first, rest⟩ := actor_journal_split leading _ journal
  cases rest with
  | cons tail => exact ⟨leading, first⟩

-- §FS-host-boundary.acceptance: Source ordinals also preserve order in the common physical journal.
theorem selected_source_length_monotone {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {before after : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime before ticks after) {first second : Nat} {left right : ActorTick runtime}
    (ordered : first ≤ second) (leftAt : ticks[first]? = some left) (rightAt : ticks[second]? = some right)
    (actor : ActorId) (initial final : EngineState)
    (initialPresent : left.before.actors actor = some initial) (finalPresent : right.before.actors actor = some final) :
    initial.events.length ≤ final.events.length := by
  induction first generalizing ticks before second with
  | zero =>
    cases journal with
    | nil => cases leftAt
    | @cons tick ticks after tail =>
      have sameTick : tick = left := Option.some.inj leftAt
      subst left
      cases second with
      | zero =>
        have sameRight : tick = right := Option.some.inj rightAt
        subst right
        have sameEngine := Option.some.inj (initialPresent.symm.trans finalPresent)
        subst initial
        exact Nat.le_refl _
      | succ second =>
        obtain ⟨middle, extra, middlePresent, shape⟩ := actor_step_event_prefix tick.operation actor initial initialPresent
        obtain ⟨leading, preceding⟩ := journal_to_selected tail rightAt
        obtain ⟨last, lastShape⟩ := actor_journal_event_prefix preceding actor middle final middlePresent finalPresent
        have lengths := congrArg List.length (lastShape.trans (congrArg (· ++ last) shape))
        simp only [List.length_append] at lengths
        omega
  | succ first ih =>
    cases second with
    | zero => omega
    | succ second =>
      cases journal with
      | nil => cases leftAt
      | cons tail => exact ih tail (by omega) leftAt rightAt

-- §FS-host-boundary.acceptance: Earlier source calls cannot be matched to later physical ticks.
theorem source_ordinal_orders_positions {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {before after : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime before ticks after) {first second : Nat} {left right : ActorTick runtime}
    (leftAt : ticks[first]? = some left) (rightAt : ticks[second]? = some right)
    (actor : ActorId) (initial final : EngineState)
    (initialPresent : left.before.actors actor = some initial) (finalPresent : right.before.actors actor = some final)
    (earlier : initial.events.length < final.events.length) : first < second := by
  apply Nat.lt_of_not_ge
  intro reversed
  have monotone := selected_source_length_monotone journal reversed rightAt leftAt actor final initial
    finalPresent initialPresent
  omega

theorem source_returns_ordered {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {before after : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime before ticks after) {actor : ActorId} {first second : Nat}
    {α β : Type} {firstEffect : Effect α} {secondEffect : Effect β} {firstReply : α} {secondReply : β}
    {firstBefore firstAfter secondBefore secondAfter : World}
    (firstSample : SourceReturnAt runtime ticks actor first α firstEffect firstReply firstBefore firstAfter)
    (secondSample : SourceReturnAt runtime ticks actor second β secondEffect secondReply secondBefore secondAfter)
    (earlier : first < second) :
    ∃ (firstPosition secondPosition : Nat) (left right : ActorTick runtime),
      ticks[firstPosition]? = some left ∧ ticks[secondPosition]? = some right ∧
      firstPosition < secondPosition ∧ left.action = .returned actor firstEffect firstReply ∧
      right.action = .returned actor secondEffect secondReply := by
  obtain ⟨firstPosition, left, initial, _, leftAt, leftAction, initialPresent, _, firstCount, _, _⟩ := firstSample
  obtain ⟨secondPosition, right, final, _, rightAt, rightAction, finalPresent, _, secondCount, _, _⟩ := secondSample
  exact ⟨firstPosition, secondPosition, left, right, leftAt, rightAt,
    source_ordinal_orders_positions journal leftAt rightAt actor initial final initialPresent finalPresent
      (by omega), leftAction, rightAction⟩

-- §FS-host-boundary.acceptance: A recorded event yields a prefix of this very engine, not a label.
theorem recorded_return_entry_prefix_for {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {actor : ActorId} {ordinal : Nat} {β : Type} {effect : Effect β} {reply : β} {before after : World}
    (sample : SourceReturnAt runtime ticks actor ordinal β effect reply before after) :
    ∃ earlier, earlier.length = ordinal ∧ Program.Prefix sourceProgram (earlier ++ [.returned effect reply]) := by
  obtain ⟨position, tick, engine, nextEngine, selected, action, present, afterPresent, count, _, _⟩ := sample
  obtain ⟨leading, trailing, shape⟩ := selected_tick_split selected
  have source := actor_journal_selected_source_for journal leading trailing tick shape actor engine present
  rcases tick with ⟨kind, population, afterPopulation, operation⟩
  dsimp only at action present source
  subst kind
  cases operation with
  | @returned γ population actualActor current operation next result world currentPresent alive head actual =>
    have same := Option.some.inj (present.symm.trans currentPresent)
    subst engine
    have reached : Residual sourceProgram current.events current.current := by
      simpa only [EngineSourceFrom, alive, Bool.true_eq, ite_true] using source
    refine ⟨current.events, count, residual_prefix reached ?_⟩
    rw [head]
    exact .returned _ _ _ [] (.empty _)

theorem recorded_return_entry_prefix {kernel : Contract} {runtime : ActorRuntime kernel}
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {actor : ActorId} {ordinal : Nat} {β : Type} {effect : Effect β} {reply : β} {before after : World}
    (sample : SourceReturnAt runtime ticks actor ordinal β effect reply before after) :
    ∃ earlier, earlier.length = ordinal ∧ Program.Prefix Entrypoint.run (earlier ++ [.returned effect reply]) :=
  recorded_return_entry_prefix_for journal sample

end LeanCage.Host.Kernel
