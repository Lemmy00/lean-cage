import GatewayWriterActiveKeys
import FilesystemIntervals

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {ticks : List (ActorTick runtime)} {pair : Pair} {Token : Type}

theorem actor_journal_keeps_actor {first last : Population} {events : List (ActorTick runtime)}
    (journal : ActorJournal runtime first events last) (actor : ActorId) (engine : EngineState)
    (present : first.actors actor = some engine) :
    ∃ next, last.actors actor = some next ∧ engine.events <+: next.events := by
  induction journal generalizing engine with
  | nil => exact ⟨engine, present, List.prefix_rfl⟩
  | @cons tick events last tail ih =>
    obtain ⟨middle, current, shape⟩ := actor_step_exact_events tick.operation actor engine present
    obtain ⟨final, finalAt, ordered⟩ := ih middle current
    exact ⟨final, finalAt, List.IsPrefix.trans ⟨_, shape.symm⟩ ordered⟩

theorem registered_actor_present
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {initialWorld : World} {finalPopulation : Population}
    (journal : ActorJournal runtime (Population.empty initialWorld) ticks finalPopulation)
    {position : Nat} {tick : ActorTick runtime} (selectedTick : ticks[position]? = some tick)
    (state : PhysicalState) (registered : Registered primitive position state)
    (actor ordinal : Nat) (current : WriteProgress) (stored : state.ledger (.engine actor ordinal) = some current) :
    ∃ engine, tick.before.actors actor = some engine ∧ ordinal ≤ engine.events.length := by
  obtain ⟨entry, token, entered, key, input, order⟩ := registered_engine_source registered actor ordinal current stored
  have fields := CallKey.engine.inj key
  obtain ⟨leading, inside, trailing, shape, interval⟩ :=
    journal_between_selected journal entry.selected selectedTick order
  obtain ⟨engine, present, eventPrefix⟩ := actor_journal_keeps_actor interval entry.actor entry.engine entry.present
  refine ⟨engine, by simpa only [fields.1] using present, ?_⟩
  rw [← fields.2]
  exact List.IsPrefix.length_le eventPrefix

private theorem same_event_history {first last : List Program.Event}
    (ordered : first <+: last) (length : first.length = last.length) : first = last := by
  obtain ⟨rest, rfl⟩ := ordered
  cases rest with
  | nil => simp
  | cons => simp only [List.length_append, List.length_cons] at length; omega

-- §AR-host-boundary.interfaces.gateway: The current dependent continuation
-- is fixed by this actor's actual source history, not just by an equal opcode.
theorem actual_same_ordinal_head {initialWorld : World} {finalPopulation : Population}
    (journal : ActorJournal runtime (Population.empty initialWorld) ticks finalPopulation)
    (entry : EngineWriteEntry ticks pair) {position : Nat} {tick : ActorTick runtime}
    (selectedTick : ticks[position]? = some tick) (engine : EngineState)
    (present : tick.before.actors entry.actor = some engine) (running : engine.running = true)
    (ordinal : engine.events.length = entry.engine.events.length) : engine.current = entry.engine.current := by
  have events : engine.events = entry.engine.events := by
    rcases Nat.le_total entry.position position with ordered | ordered
    · exact (same_event_history
        (selected_events_prefix journal ordered entry.selected selectedTick entry.actor entry.engine engine
          entry.present present) ordinal.symm).symm
    · exact same_event_history
        (selected_events_prefix journal ordered selectedTick entry.selected entry.actor engine entry.engine
          present entry.present) ordinal
  obtain ⟨firstLeading, firstTrailing, _, firstShape⟩ := selected_tick_exact_split entry.selected
  obtain ⟨lastLeading, lastTrailing, _, lastShape⟩ := selected_tick_exact_split selectedTick
  have before := selected_actor_head_for journal firstLeading firstTrailing entry.tick firstShape entry.present entry.running
  have after := selected_actor_head_for journal lastLeading lastTrailing tick lastShape present running
  rw [events] at after
  exact residual_current_unique after before

-- The row synchronizer has no source-entry constructors, so all older ACKs
-- stay closed even when the current row is unrelated, interrupted or lost.
theorem EngineRow.older_returned
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {position : Nat} {tick : ActorTick runtime} {initial final : PhysicalState} {records : List Record}
    (row : EngineRow primitive position tick initial records final) (actor ordinal : Nat)
    (before : OlderReturned actor ordinal initial.ledger) : OlderReturned actor ordinal final.ledger := by
  apply row.run.older_returned actor ordinal before
  cases row with
  | absent | outside => simp
  | acknowledged entry reply observation atPosition sameTick =>
    intro record member key input event
    cases List.mem_singleton.mp member
    cases reply <;> cases event

-- §FS-host-boundary.caller: Advancing an actual returned source event closes
-- its exact registered call; the ACK contributes no payload a second time.
theorem EngineRow.returned_key
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {position : Nat} {tick : ActorTick runtime} {initial final : PhysicalState} {records : List Record}
    (row : EngineRow primitive position tick initial records final)
    (observation : WriteObservation) (selected : writeObservationAt tick = some observation)
    (reply : Reply) (returned : observation.reply = some reply) :
    ∀ current, final.ledger observation.key = some current → current.observation = .returned reply := by
  intro current stored
  cases row with
  | absent none => rw [none] at selected; cases selected
  | outside other scan unregistered outside =>
    have same := Option.some.inj (scan.symm.trans selected)
    subst other
    rw [unregistered] at stored
    cases stored
  | acknowledged entry answer actual atPosition sameTick =>
    have scan := write_observation_complete actual.source.tick entry.actor actual.source.engine
      actual.source.present entry.request answer entry.writing actual.source.action
    rw [actual.source.ordinal, sameTick, selected] at scan
    have identity := Option.some.inj scan
    subst observation
    dsimp only at returned
    subst answer
    simp only [Ledger.set, WriteObservation.key, EngineWriteEntry.key, ite_true,
      Option.some.injEq] at stored
    subst current
    rfl

theorem EngineRow.entry_existed
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {position : Nat} {tick : ActorTick runtime} {initial final : PhysicalState} {records : List Record}
    (row : EngineRow primitive position tick initial records final) (key : CallKey)
    (current : WriteProgress) (stored : final.ledger key = some current) :
    ∃ previous, initial.ledger key = some previous := by
  cases row with
  | absent | outside => exact ⟨current, stored⟩
  | acknowledged entry reply actual atPosition sameTick =>
    by_cases same : key = entry.key
    · subst key
      exact ⟨actual.current, actual.selected⟩
    · exact ⟨current, by simpa only [Ledger.set, ite_eq_right same] using stored⟩

def SourceAligned (population : Population) (ledger : Ledger) : Prop :=
  ∀ actor engine, population.actors actor = some engine → engine.running = true →
    OlderReturned actor engine.events.length ledger

theorem SourceAligned.pending
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {position : Nat} {tick : ActorTick runtime} {initial final : PhysicalState} {records : List Record}
    (selectedTick : ticks[position]? = some tick)
    (batch : PendingBatch primitive position initial final records)
    (aligned : SourceAligned tick.before initial.ledger) : SourceAligned tick.before final.ledger := by
  intro actor engine present running
  exact batch.older_returned tick selectedTick actor engine present (aligned actor engine present running)

end LeanCage.Host.PrivateStreams
