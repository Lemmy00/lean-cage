import FilesystemRuntime
import FilesystemReferences

namespace LeanCage.Host.Kernel
open Filesystem

variable {sourceProgram : Program UInt32}

def CompatibleInterference (before after : World) : Prop :=
  after.handles = before.handles ∧ after.closeOnExec = before.closeOnExec ∧
    after.workingDirectory = before.workingDirectory ∧
    (∀ object, before.allocated object = true → after.allocated object = true) ∧
    (∀ id, before.descriptionAllocated id = true → after.descriptionAllocated id = true) ∧
    (∀ fd handle, before.handles fd = some handle → ∃ description,
      after.descriptions handle.description = some description ∧ description.object = handle.object)

-- §AR-host-boundary.primitives: This conservative environment abstraction leaves shared data free.
structure InterferenceContract (kernel : Contract) : Prop where
  compatible : ∀ before after, CompatibleInterference before after → kernel.interference before after

-- §AR-host-boundary.primitives: These are projections of one shared kernel action, not region
-- frames.
structure ProjectionContract {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram) : Prop where
  returned : ∀ {β : Type} (population : Population) actor (engine : EngineState) (effect : Effect β)
    next reply world query (other : EngineState),
    population.actors actor = some engine → engine.running = true → engine.current = .call effect next →
    ActorOperation runtime actor effect (some reply) (population.project engine) world →
    population.actors query = some other → query ≠ actor →
    population.Consistent →
    kernel.interference (population.project other)
      ((population.advance actor (engine.returned effect reply next world) world).project other)
  lost : ∀ {β : Type} (population : Population) actor (engine : EngineState) (effect : Effect β)
    next world query (other : EngineState),
    population.actors actor = some engine → engine.running = true → engine.current = .call effect next →
    ActorOperation runtime actor effect none (population.project engine) world →
    population.actors query = some other → query ≠ actor →
    population.Consistent →
    kernel.interference (population.project other)
      ((population.advance actor (engine.lost effect world) world).project other)
  foreign : ∀ (population : Population) caller world query (engine : EngineState),
    runtime.foreign caller population.shared world → population.actors query = some engine → population.Consistent →
    kernel.interference (population.project engine) ({population with shared := world}.project engine)
  retire : ∀ (population : Population) actor (engine : EngineState) observation world query (other : EngineState),
    population.actors actor = some engine →
    runtime.retire actor observation engine.directory (population.project engine) world →
    population.actors query = some other → query ≠ actor → population.Consistent →
    kernel.interference (population.project other)
      ((population.advance actor (engine.retired observation world) world).project other)
  nativeRetire : ∀ (population : Population) token observation beforeResources afterResources world query (engine : EngineState),
    runtime.nativeRetire token observation beforeResources afterResources population.shared world →
    population.actors query = some engine → population.Consistent →
    kernel.interference (population.project engine) ({population with shared := world}.project engine)

-- §AR-host-boundary.primitives: Projection is derived from individual reference laws on valid
-- views.
theorem projection_from_reference_laws {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (environment : InterferenceContract kernel) :
    ProjectionContract runtime := by
  constructor
  · intro β population actor engine effect next reply world query other present alive head actual otherPresent different valid
    have preserved := operation_retains_references descriptors lifetimes references actual (valid query other otherPresent)
    apply environment.compatible
    refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
    · intro object allocated
      exact operation_allocated lifetimes actual object allocated
    · intro id allocated
      exact operation_description_allocated references actual id allocated
    · intro fd handle live
      exact (preserved fd handle live).2.2
  · intro β population actor engine effect next world query other present alive head actual otherPresent different valid
    have preserved := operation_retains_references descriptors lifetimes references actual (valid query other otherPresent)
    apply environment.compatible
    refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
    · intro object allocated
      exact operation_allocated lifetimes actual object allocated
    · intro id allocated
      exact operation_description_allocated references actual id allocated
    · intro fd handle live
      exact (preserved fd handle live).2.2
  · intro population caller world query engine actual present valid
    apply environment.compatible
    refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
    · intro object allocated
      exact lifetimes.foreign caller population.shared world object actual allocated
    · intro id allocated
      exact references.foreign_description caller population.shared world id actual allocated
    · intro fd handle live
      obtain ⟨_, _, description, recorded, same⟩ := valid query engine present fd handle live
      obtain ⟨later, recordedLater, sameLater⟩ := references.foreign_identity _ _ _ _ _ actual recorded
      exact ⟨later, recordedLater, sameLater.trans same⟩
  · intro population actor engine observation world query other present actual otherPresent different valid
    apply environment.compatible
    refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
    · exact fun object => lifetimes.retire actor observation engine.directory (population.project engine) world object actual
    · exact fun id => references.retire_description actor observation engine.directory (population.project engine) world id actual
    · intro fd handle live
      obtain ⟨_, _, description, recorded, same⟩ := valid query other otherPresent fd handle live
      obtain ⟨later, recordedLater, sameLater⟩ := references.retire_identity actor observation engine.directory (population.project engine) world _ _ actual recorded
      exact ⟨later, recordedLater, sameLater.trans same⟩
  · intro population token observation beforeResources afterResources world query engine actual present valid
    apply environment.compatible
    refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
    · exact fun object => lifetimes.nativeRetire token observation beforeResources afterResources population.shared world object actual
    · exact fun id => references.native_retire_description token observation beforeResources afterResources population.shared world id actual
    · intro fd handle live
      obtain ⟨_, _, description, recorded, same⟩ := valid query engine present fd handle live
      obtain ⟨later, recordedLater, sameLater⟩ := references.native_retire_identity token observation beforeResources afterResources population.shared world _ _ actual recorded
      exact ⟨later, recordedLater, sameLater.trans same⟩

inductive ActorReturnsHistory {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram) (actor : ActorId) :
    World → List Program.Event → World → Prop where
  | nil (world : World) : ActorReturnsHistory runtime actor world [] world
  | returned {β : Type} {effect : Effect β} {reply : β} {before middle after : World}
      {events : List Program.Event} (actual : ActorOperation runtime actor effect (some reply) before middle)
      (tail : ActorReturnsHistory runtime actor middle events after) :
      ActorReturnsHistory runtime actor before (.returned effect reply :: events) after
  | environment {before middle after : World} {events : List Program.Event}
      (interference : kernel.interference before middle)
      (tail : ActorReturnsHistory runtime actor middle events after) :
      ActorReturnsHistory runtime actor before events after

abbrev OperationOrigin := Nat → (β : Type) → Effect β → β → World → World → Prop

inductive ActorHistoryWith {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram) (actor : ActorId)
    (origin : OperationOrigin) : Nat → World → List Program.Event → World → Prop where
  | nil (ordinal : Nat) (world : World) : ActorHistoryWith runtime actor origin ordinal world [] world
  | returned {β : Type} {effect : Effect β} {reply : β} {before middle after : World}
      {ordinal : Nat} {events : List Program.Event} (actual : ActorOperation runtime actor effect (some reply) before middle)
      (recorded : origin ordinal β effect reply before middle)
      (tail : ActorHistoryWith runtime actor origin (ordinal + 1) middle events after) :
      ActorHistoryWith runtime actor origin ordinal before (.returned effect reply :: events) after
  | environment {before middle after : World} {ordinal : Nat} {events : List Program.Event}
      (interference : kernel.interference before middle) (tail : ActorHistoryWith runtime actor origin ordinal middle events after) :
      ActorHistoryWith runtime actor origin ordinal before events after

def Captures {kernel : Contract} (runtime : ActorRuntime kernel sourceProgram) (actor : ActorId)
    (origin : OperationOrigin) (ticks : List (ActorTick runtime)) : Prop :=
  ∀ tick ∈ ticks, ∀ {β : Type} (effect : Effect β) (reply : β) (initial final : EngineState),
    tick.action = .returned actor effect reply → tick.before.actors actor = some initial →
    tick.after.actors actor = some final → origin initial.events.length β effect reply (tick.before.project initial) (tick.after.project final)

theorem actor_history_erase {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram} {actor : ActorId}
    {origin : OperationOrigin} {ordinal : Nat} {before after : World} {events : List Program.Event}
    (history : ActorHistoryWith runtime actor origin ordinal before events after) :
    ActorReturnsHistory runtime actor before events after := by
  induction history with
  | nil => exact .nil _
  | returned actual recorded tail ih => exact .returned actual ih
  | environment interference tail ih => exact .environment interference ih

def Population.Dead (population : Population) (actor : ActorId) : Prop :=
  ∃ engine, population.actors actor = some engine ∧ engine.running = false

theorem actor_step_dead {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {before after : Population} {action : ActorAction} (step : ActorStep runtime action before after)
    (query : ActorId) (dead : before.Dead query) : after.Dead query := by
  obtain ⟨previous, previousPresent, previousDead⟩ := dead
  cases step with
  | @launch population actor references closeExec workingDirectory fresh absent inherited =>
    have different : query ≠ actor := by intro same; subst query; rw [absent] at previousPresent; cases previousPresent
    exact ⟨previous, by simpa only [Population.launch, Population.install, ite_eq_right different] using previousPresent,
      previousDead⟩
  | @returned β population actor engine effect next reply world present alive head actual =>
    have different : query ≠ actor := by
      intro same
      subst query
      have sameEngine := Option.some.inj (present.symm.trans previousPresent)
      subst previous
      rw [alive] at previousDead
      cases previousDead
    exact ⟨previous, by simpa only [Population.advance, Population.install, ite_eq_right different] using previousPresent,
      previousDead⟩
  | @lost β population actor engine effect next world present alive head actual =>
    have different : query ≠ actor := by
      intro same
      subst query
      have sameEngine := Option.some.inj (present.symm.trans previousPresent)
      subst previous
      rw [alive] at previousDead
      cases previousDead
    exact ⟨previous, by simpa only [Population.advance, Population.install, ite_eq_right different] using previousPresent,
      previousDead⟩
  | foreign actual => exact ⟨previous, previousPresent, previousDead⟩
  | @retire population actor engine observation world present actual =>
    by_cases same : query = actor
    · subst query
      exact ⟨engine.retired observation world, by simp [Population.advance, Population.install], rfl⟩
    · exact ⟨previous, by
        simpa only [Population.advance, Population.install, ite_eq_right same] using previousPresent, previousDead⟩
  | nativeRetire actual => exact ⟨previous, previousPresent, previousDead⟩

theorem actor_journal_dead {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    {before after : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime before ticks after) (query : ActorId) (dead : before.Dead query) :
    after.Dead query := by
  induction journal with
  | nil => exact dead
  | @cons tick ticks after tail ih => exact ih (actor_step_dead tick.operation query dead)

-- §FS-host-boundary.acceptance: Project actual calls and all intervening peer changes on one actor.
theorem actor_journal_projection_with {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (laws : ProjectionContract runtime) {before after : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime before ticks after) (consistent : JournalConsistent ticks)
    (query : ActorId) (origin : OperationOrigin) (captures : Captures runtime query origin ticks)
    (initial final : EngineState)
    (initialPresent : before.actors query = some initial) (initialLive : initial.running = true)
    (finalPresent : after.actors query = some final) (finalLive : final.running = true) :
    ∃ events, final.events = initial.events ++ events ∧ Residual initial.current events final.current ∧
      ActorHistoryWith runtime query origin initial.events.length (before.project initial) events (after.project final) := by
  induction journal generalizing initial with
  | nil population =>
    have same := Option.some.inj (initialPresent.symm.trans finalPresent)
    subst initial
    exact ⟨[], by simp, .refl _, .nil _ _⟩
  | @cons tick ticks after tail ih =>
    have valid := (consistent tick (by simp)).1
    have restConsistent : JournalConsistent ticks := by
      intro selected member
      exact consistent selected (by simp [member])
    have restCaptures : Captures runtime query origin ticks := by
      intro selected member
      exact captures selected (by simp [member])
    rcases tick with ⟨action, population, middle, operation⟩
    cases operation with
    | @launch population actor references closeExec workingDirectory fresh absent inherited =>
      have different : query ≠ actor := by intro same; subst query; rw [absent] at initialPresent; cases initialPresent
      have middlePresent : (population.launch actor (.initialFrom sourceProgram references closeExec workingDirectory)).actors query = some initial := by
        simpa only [Population.launch, Population.install, ite_eq_right different] using initialPresent
      exact ih restConsistent restCaptures initial middlePresent initialLive finalPresent
    | @returned β population actor engine effect next reply world present alive head actual =>
      by_cases sameActor : query = actor
      · subst actor
        have sameEngine := Option.some.inj (initialPresent.symm.trans present)
        subst engine
        let advanced := initial.returned effect reply next world
        have middlePresent : (population.advance query advanced world).actors query = some advanced := by
          simp [Population.advance, Population.install]
        obtain ⟨events, shape, source, history⟩ := ih restConsistent restCaptures advanced middlePresent rfl finalPresent
        refine ⟨.returned effect reply :: events, ?_, ?_, ?_⟩
        · simpa only [EngineState.returned, advanced, List.append_assoc, List.singleton_append] using shape
        · rw [head]
          exact .call source
        · have sample := captures _ List.mem_cons_self effect reply initial advanced
            rfl initialPresent middlePresent
          apply ActorHistoryWith.returned actual sample
          simpa only [EngineState.returned, Population.project, Population.advance, advanced,
            List.length_append, List.length_singleton] using history
      · have middlePresent : (population.advance actor (engine.returned effect reply next world) world).actors query =
            some initial := by
          simpa only [Population.advance, Population.install, ite_eq_right sameActor] using initialPresent
        obtain ⟨events, shape, source, history⟩ := ih restConsistent restCaptures initial middlePresent initialLive finalPresent
        exact ⟨events, shape, source, .environment
          (laws.returned population actor engine effect next reply world query initial present alive head actual
            initialPresent sameActor valid) history⟩
    | @lost β population actor engine effect next world present alive head actual =>
      by_cases sameActor : query = actor
      · subst actor
        let stopped := engine.lost effect world
        have dead : (population.advance query stopped world).Dead query := by
          refine ⟨stopped, ?_, rfl⟩
          simp [Population.advance, Population.install]
        obtain ⟨last, lastPresent, lastDead⟩ := actor_journal_dead tail query dead
        have sameEngine := Option.some.inj (finalPresent.symm.trans lastPresent)
        subst last
        rw [finalLive] at lastDead
        cases lastDead
      · have middlePresent : (population.advance actor (engine.lost effect world) world).actors query = some initial := by
          simpa only [Population.advance, Population.install, ite_eq_right sameActor] using initialPresent
        obtain ⟨events, shape, source, history⟩ := ih restConsistent restCaptures initial middlePresent initialLive finalPresent
        exact ⟨events, shape, source, .environment
          (laws.lost population actor engine effect next world query initial present alive head actual
            initialPresent sameActor valid) history⟩
    | @foreign population caller world actual =>
      obtain ⟨events, shape, source, history⟩ := ih restConsistent restCaptures initial initialPresent initialLive finalPresent
      exact ⟨events, shape, source,
        .environment (laws.foreign population caller world query initial actual initialPresent valid) history⟩
    | @retire population actor engine observation world present actual =>
      by_cases sameActor : query = actor
      · subst actor
        let stopped := engine.retired observation world
        have dead : (population.advance query stopped world).Dead query := by
          exact ⟨stopped, by simp [Population.advance, Population.install], rfl⟩
        obtain ⟨last, lastPresent, lastDead⟩ := actor_journal_dead tail query dead
        have identity := Option.some.inj (finalPresent.symm.trans lastPresent)
        subst last
        rw [finalLive] at lastDead
        cases lastDead
      · have middlePresent : (population.advance actor (engine.retired observation world) world).actors query = some initial := by
          simpa only [Population.advance, Population.install, ite_eq_right sameActor] using initialPresent
        obtain ⟨events, shape, source, history⟩ := ih restConsistent restCaptures initial middlePresent initialLive finalPresent
        exact ⟨events, shape, source, .environment
          (laws.retire population actor engine observation world query initial present actual initialPresent sameActor valid) history⟩
    | @nativeRetire population token observation beforeResources afterResources world actual =>
      obtain ⟨events, shape, source, history⟩ := ih restConsistent restCaptures initial initialPresent initialLive finalPresent
      exact ⟨events, shape, source,
        .environment (laws.nativeRetire population token observation beforeResources afterResources world query initial actual
          initialPresent valid) history⟩

theorem actor_journal_projection {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (laws : ProjectionContract runtime) {before after : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime before ticks after) (consistent : JournalConsistent ticks)
    (query : ActorId) (initial final : EngineState)
    (initialPresent : before.actors query = some initial) (initialLive : initial.running = true)
    (finalPresent : after.actors query = some final) (finalLive : final.running = true) :
    ∃ events, final.events = initial.events ++ events ∧ Residual initial.current events final.current ∧
      ActorReturnsHistory runtime query (before.project initial) events (after.project final) := by
  let origin : OperationOrigin := fun _ _ _ _ _ _ => True
  have captures : Captures runtime query origin ticks := by intro tick member β effect reply first last action initial final; trivial
  obtain ⟨events, shape, source, history⟩ := actor_journal_projection_with laws journal consistent query origin captures
    initial final initialPresent initialLive finalPresent finalLive
  exact ⟨events, shape, source, actor_history_erase history⟩

theorem actual_actor_projection {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram}
    (descriptors : DescriptorContract kernel) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (environment : InterferenceContract kernel)
    {before after : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime before ticks after) (valid : before.Consistent)
    (actor : ActorId) (initial final : EngineState)
    (initialPresent : before.actors actor = some initial) (initialLive : initial.running = true)
    (finalPresent : after.actors actor = some final) (finalLive : final.running = true) :
    ∃ events, final.events = initial.events ++ events ∧ Residual initial.current events final.current ∧
      ActorReturnsHistory runtime actor (before.project initial) events (after.project final) :=
  actor_journal_projection (projection_from_reference_laws descriptors lifetimes references environment)
    journal (actor_journal_consistent descriptors lifetimes references journal valid).2
    actor initial final initialPresent initialLive finalPresent finalLive

theorem actor_history_append {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram} {actor : ActorId}
    {before middle after : World} {first last : List Program.Event}
    (initial : ActorReturnsHistory runtime actor before first middle)
    (final : ActorReturnsHistory runtime actor middle last after) :
    ActorReturnsHistory runtime actor before (first ++ last) after := by
  induction initial with
  | nil => exact final
  | returned actual tail ih => exact .returned actual (ih final)
  | environment interference tail ih => exact .environment interference (ih final)

theorem actor_history_head {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram} {actor : ActorId}
    {β : Type} {effect : Effect β} {reply : β} {before after : World} {events : List Program.Event}
    (history : ActorReturnsHistory runtime actor before (.returned effect reply :: events) after) :
    ∃ actual middle, ActorReturnsHistory runtime actor before [] actual ∧
      ActorOperation runtime actor effect (some reply) actual middle ∧
      ActorReturnsHistory runtime actor middle events after := by
  generalize shape : .returned effect reply :: events = all at history
  induction history with
  | nil => cases shape
  | returned actual tail ih => cases shape; exact ⟨_, _, .nil _, actual, tail⟩
  | environment interference tail ih =>
    obtain ⟨actual, middle, first, operation, rest⟩ := ih shape
    exact ⟨actual, middle, .environment interference first, operation, rest⟩

private theorem actor_history_no_lost {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram} {actor : ActorId}
    {β : Type} {effect : Effect β} {before after : World} {events : List Program.Event} :
    ¬ ActorReturnsHistory runtime actor before (.lost effect :: events) after := by
  intro history
  generalize shape : .lost effect :: events = all at history
  induction history with
  | nil => cases shape
  | returned actual tail ih => cases shape
  | environment interference tail ih => exact ih shape

theorem actor_history_split {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram} {actor : ActorId}
    {before after : World} (first last : List Program.Event)
    (history : ActorReturnsHistory runtime actor before (first ++ last) after) :
    ∃ middle, ActorReturnsHistory runtime actor before first middle ∧ ActorReturnsHistory runtime actor middle last after := by
  induction first generalizing before with
  | nil => exact ⟨before, .nil _, history⟩
  | cons event rest ih =>
    cases event with
    | lost effect => exact False.elim (actor_history_no_lost history)
    | returned effect reply =>
      obtain ⟨actual, between, leading, operation, tail⟩ := actor_history_head history
      obtain ⟨middle, initial, final⟩ := ih tail
      exact ⟨middle, actor_history_append leading (.returned operation initial), final⟩

theorem actor_filesystem_history {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram} {actor : ActorId}
    {before after : World} {events : List (Request × Reply)}
    (history : ActorReturnsHistory runtime actor before (events.map Program.filesystemEvent) after) :
    History kernel before events after := by
  generalize shape : events.map Program.filesystemEvent = all at history
  induction history generalizing events with
  | nil => cases events <;> cases shape; exact .nil _
  | returned operation tail ih =>
    cases events with
    | nil => cases shape
    | cons event rest =>
      cases event with
      | mk request reply =>
        cases shape
        exact .cons operation (ih rfl)
  | environment interference tail ih => exact .environment interference (ih shape)

-- §FS-host-boundary.acceptance: Earlier source phase returns become physical runs on this same
-- history.
theorem actor_filesystem_phase {kernel : Contract} {runtime : ActorRuntime kernel sourceProgram} {actor : ActorId}
    {α : Type} {program : Filesystem.Program α} {before after : World} {context tail : List Program.Event}
    {events : List (Request × Reply)} {value : α}
    (history : ActorReturnsHistory runtime actor before (context ++ events.map Program.filesystemEvent ++ tail) after)
    (source : Returns program events value) :
    ∃ first last, ActorReturnsHistory runtime actor before context first ∧
      ConcurrentRun kernel program first events last value ∧ ActorReturnsHistory runtime actor last tail after := by
  rw [List.append_assoc] at history
  obtain ⟨first, leading, rest⟩ := actor_history_split context _ history
  obtain ⟨last, phase, final⟩ := actor_history_split (events.map Program.filesystemEvent) tail rest
  exact ⟨first, last, leading, ⟨source, actor_filesystem_history phase⟩, final⟩

end LeanCage.Host.Kernel
