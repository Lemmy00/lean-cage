import GatewayWriterRows

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {ticks : List (ActorTick runtime)} {pair : Pair} {Token : Type}

-- §AR-host-boundary.primitives: This is the single actual ACK/loss sample of
-- a registered pending call, not a frame or a whole completed writer premise.
structure EngineAckSample
    (primitive : Primitive process child native hostUid before after callers next ticks pair Token)
    (position : Nat) (entry : EngineWriteEntry ticks pair) (reply : Option Reply)
    (state : PhysicalState) where
  token : Token
  entered : primitive.enteredEngine token entry
  current : WriteProgress
  selected : state.ledger entry.key = some current
  stream : State
  live : state.stream = some stream
  final : State
  observed : primitive.observation position token current reply stream final

-- This is a raw current descriptor observation at one actual source row.
-- It grants no invocation role, private-root or queue safety assertion.
def OutsidePair (pair : Pair) (tick : ActorTick runtime) (actual : WriteObservation) : Prop :=
  ∀ engine, tick.before.actors actual.actor = some engine →
    ∀ handle, engine.references actual.request.first = some handle →
      handle.object ≠ pair.caller ∧ handle.object ≠ pair.engine

-- §FS-host-boundary.caller: EVERY actual write reply/loss is processed. A row
-- can be outside this channel only when its exact call key is unregistered.
inductive EngineRow
    (primitive : Primitive process child native hostUid before after callers next ticks pair Token)
    (position : Nat) (tick : ActorTick runtime) (initial : PhysicalState) :
    List Record → PhysicalState → Type 1 where
  | absent (none : writeObservationAt tick = none) : EngineRow primitive position tick initial [] initial
  | outside (actual : WriteObservation) (selected : writeObservationAt tick = some actual)
      (unregistered : initial.ledger actual.key = none) (outside : OutsidePair pair tick actual) : EngineRow primitive position tick initial [] initial
  | acknowledged (entry : EngineWriteEntry ticks pair) (reply : Option Reply)
      (actual : EngineReconciliation primitive entry reply initial)
      (atPosition : actual.source.position = position) (sameTick : actual.source.tick = tick) :
      EngineRow primitive position tick initial
        [⟨position, observationEvent entry.key reply, []⟩]
        { stream := some actual.final
          ledger := initial.ledger.set entry.key (observed actual.current reply) }

structure EngineRowSamples
    (primitive : Primitive process child native hostUid before after callers next ticks pair Token)
    (position : Nat) (tick : ActorTick runtime) (state : PhysicalState) where
  outside : ∀ actual, writeObservationAt tick = some actual → state.ledger actual.key = none →
    OutsidePair pair tick actual
  observation : ∀ (entry : EngineWriteEntry ticks pair) reply,
    writeObservationAt tick = some ⟨entry.actor, entry.engine.events.length, entry.request, reply⟩ →
    state.ledger entry.key ≠ none → Nonempty (EngineAckSample primitive position entry reply state)

-- The source journal identifies the request from the SAME actor/ordinal. The
-- physical boundary supplies only its actual count/loss observation; it never
-- assumes that the descriptor still exists when the ACK becomes visible.
theorem actual_engine_row
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {initialWorld : World} {finalPopulation : Population}
    (journal : ActorJournal runtime (Population.empty initialWorld) ticks finalPopulation)
    (position : Nat) (tick : ActorTick runtime) (selectedTick : ticks[position]? = some tick)
    (state : PhysicalState) (registered : Registered primitive position state)
    (samples : EngineRowSamples primitive position tick state) :
    ∃ records final, Nonempty (EngineRow primitive position tick state records final) := by
  classical
  cases scan : writeObservationAt tick with
  | none => exact ⟨[], state, ⟨.absent scan⟩⟩
  | some actual =>
    cases stored : state.ledger actual.key with
    | none => exact ⟨[], state, ⟨.outside actual scan stored (samples.outside actual scan stored)⟩⟩
    | some current =>
      obtain ⟨entry, token, entered, key, input, order⟩ :=
        registered_engine_source registered actual.actor actual.ordinal current stored
      have keys := CallKey.engine.inj key
      obtain ⟨engine, present, ordinal, writing, action⟩ := write_observation_fields tick actual scan
      have sameActor : entry.actor = actual.actor := keys.1
      have sameOrdinal : entry.engine.events.length = actual.ordinal := keys.2
      have atActor : tick.before.actors entry.actor = some engine := by simpa only [sameActor] using present
      have atOrdinal : engine.events.length = entry.engine.events.length := ordinal.trans sameOrdinal.symm
      obtain ⟨original, next, originalPresent, running, head⟩ :=
        actual_filesystem_observation_head tick.operation entry.actor actual.request actual.reply
          (by simpa only [sameActor] using action)
      have identity := Option.some.inj (atActor.symm.trans originalPresent)
      subst original
      have sameRequest : entry.request = actual.request :=
        (actual_same_ordinal_request journal entry selectedTick engine atActor running atOrdinal actual.request next head).symm
      let source : EngineObservation entry actual.reply :=
        ⟨position, tick, selectedTick, engine, atActor, atOrdinal, by simpa only [sameRequest, sameActor] using action⟩
      have exactScan : writeObservationAt tick =
          some ⟨entry.actor, entry.engine.events.length, entry.request, actual.reply⟩ := by
        simpa only [sameActor, sameOrdinal, sameRequest] using scan
      have nonempty : state.ledger entry.key ≠ none := by
        rw [key]
        change state.ledger actual.key ≠ none
        rw [stored]
        simp
      obtain ⟨sample⟩ := samples.observation entry actual.reply exactScan nonempty
      let result : EngineReconciliation primitive entry actual.reply state :=
        ⟨source, sample.token, sample.entered, sample.current, sample.selected,
          sample.stream, sample.live, sample.final, sample.observed⟩
      exact ⟨_, _, ⟨.acknowledged entry actual.reply result rfl rfl⟩⟩

def EngineRow.run
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {position : Nat} {tick : ActorTick runtime} {initial final : PhysicalState} {records : List Record}
    (row : EngineRow primitive position tick initial records final) :
    ObservedJournal primitive position initial records final := by
  cases row with
  | absent | outside => exact .nil _ _
  | acknowledged entry reply actual atPosition sameTick =>
    subst position
    exact .cons (Nat.le_refl _) actual.step (.nil _ _)

theorem EngineRow.queue_unchanged
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {position : Nat} {tick : ActorTick runtime} {initial final : PhysicalState} {records : List Record}
    (row : EngineRow primitive position tick initial records final) : final.stream = initial.stream := by
  cases row with
  | absent | outside => rfl
  | acknowledged entry reply actual atPosition sameTick => rw [actual.exact.1]; exact actual.live.symm

def replyObservation : Option Reply → Observation
  | none => .lost
  | some reply => .returned reply

theorem EngineRow.covers
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {position : Nat} {tick : ActorTick runtime} {initial final : PhysicalState} {records : List Record}
    (row : EngineRow primitive position tick initial records final)
    (actual : WriteObservation) (selected : writeObservationAt tick = some actual)
    (current : WriteProgress) (stored : initial.ledger actual.key = some current) :
    ∃ last, final.ledger actual.key = some last ∧ last.input = current.input ∧
      last.committed = current.committed ∧ last.observation = replyObservation actual.reply := by
  cases row with
  | absent none => rw [none] at selected; cases selected
  | outside other scan unregistered outside =>
    have same := Option.some.inj (scan.symm.trans selected)
    subst other
    rw [unregistered] at stored
    cases stored
  | acknowledged entry reply observation atPosition sameTick =>
    have scan := write_observation_complete observation.source.tick entry.actor observation.source.engine
      observation.source.present entry.request reply entry.writing observation.source.action
    rw [observation.source.ordinal, sameTick, selected] at scan
    have identity := Option.some.inj scan
    subst actual
    change initial.ledger entry.key = some current at stored
    have sameCurrent := Option.some.inj (observation.selected.symm.trans stored)
    subst current
    exact ⟨observed observation.current reply, by simp [Ledger.set, WriteObservation.key, EngineWriteEntry.key],
      by cases reply <;> rfl, by cases reply <;> rfl, by cases reply <;> rfl⟩

theorem EngineRow.positions
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {position : Nat} {tick : ActorTick runtime} {initial final : PhysicalState} {records : List Record}
    (row : EngineRow primitive position tick initial records final) :
    ∀ record ∈ records, record.position = position := by
  cases row with
  | absent | outside => simp
  | acknowledged => intro record member; cases List.mem_singleton.mp member; rfl

-- §FS-host-boundary.caller: An actual inherited IPC write cannot use the
-- unregistered branch. Every such ACK/loss therefore has an actual source
-- entry and a single matching ledger update, regardless of its count.
theorem EngineRow.private_ack
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {position : Nat} {tick : ActorTick runtime} {initial final : PhysicalState} {records : List Record}
    (row : EngineRow primitive position tick initial records final)
    (actual : WriteObservation) (selected : writeObservationAt tick = some actual)
    (engine : EngineState) (present : tick.before.actors actual.actor = some engine)
    (handle : Handle) (input : engine.references actual.request.first = some handle)
    (privateEndpoint : handle.object = pair.caller ∨ handle.object = pair.engine) :
    ∃ entry : EngineWriteEntry ticks pair,
      entry.actor = actual.actor ∧ entry.engine.events.length = actual.ordinal ∧
      entry.request = actual.request ∧
      ∃ observation : EngineReconciliation primitive entry actual.reply initial,
        observation.source.position = position ∧ observation.source.tick = tick ∧
        final.ledger actual.key = some (observed observation.current actual.reply) := by
  cases row with
  | absent none => rw [none] at selected; cases selected
  | outside other scan unregistered outside =>
    have same := Option.some.inj (scan.symm.trans selected)
    subst other
    have exclusions := outside engine present handle input
    exact False.elim (privateEndpoint.elim exclusions.1 exclusions.2)
  | acknowledged entry reply observation atPosition sameTick =>
    have scan := write_observation_complete observation.source.tick entry.actor observation.source.engine
      observation.source.present entry.request reply entry.writing observation.source.action
    rw [observation.source.ordinal, sameTick, selected] at scan
    have identity := Option.some.inj scan
    subst actual
    exact ⟨entry, rfl, rfl, rfl, observation, atPosition, sameTick, by
      simp [Ledger.set, WriteObservation.key, EngineWriteEntry.key]⟩

end LeanCage.Host.PrivateStreams
