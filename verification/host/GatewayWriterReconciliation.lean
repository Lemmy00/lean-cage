import GatewayStreamJournal
import GatewayWriterAcknowledgements
import GatewayActorCallIdentity

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {ticks : List (ActorTick runtime)} {pair : Pair} {Token : Type}

theorem registered_engine_source
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {position : Nat} {state : PhysicalState} (registered : Registered primitive position state)
    (actor ordinal : Nat) (current : WriteProgress)
    (selected : state.ledger (.engine actor ordinal) = some current) :
    ∃ entry token, primitive.enteredEngine token entry ∧ entry.key = .engine actor ordinal ∧
      entry.description = current.input ∧ entry.position ≤ position := by
  have origin := registered (.engine actor ordinal) current selected
  generalize keyIdentity : CallKey.engine actor ordinal = key at origin
  generalize inputIdentity : current.input = input at origin
  cases origin with
  | engine entry token entered order =>
    exact ⟨entry, token, entered, rfl, rfl, order⟩
  | native entry token entered order => cases keyIdentity

-- §AR-host-boundary.primitives: An ACK/loss names the actual actor lifetime,
-- raw ordinal and request. It does not require the FD still to be open at ACK.
structure EngineObservation (entry : EngineWriteEntry ticks pair) (reply : Option Reply) where
  position : Nat
  tick : ActorTick runtime
  selected : ticks[position]? = some tick
  engine : EngineState
  present : tick.before.actors entry.actor = some engine
  ordinal : engine.events.length = entry.engine.events.length
  action : tick.action.eventFor entry.actor = some (Program.filesystemPrefixEvent (entry.request, reply))

theorem actual_engine_observation {initial : World} {final : Population}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    (entry : EngineWriteEntry ticks pair) {position : Nat} {tick : ActorTick runtime}
    (selected : ticks[position]? = some tick) (engine : EngineState)
    (present : tick.before.actors entry.actor = some engine)
    (ordinal : engine.events.length = entry.engine.events.length)
    (request : Request) (reply : Option Reply)
    (observed : tick.action.eventFor entry.actor = some (Program.filesystemPrefixEvent (request, reply))) :
    Nonempty (EngineObservation entry reply) := by
  obtain ⟨actual, next, actualPresent, running, head⟩ :=
    actual_filesystem_observation_head tick.operation entry.actor request reply observed
  have identity := Option.some.inj (present.symm.trans actualPresent)
  subst actual
  have same := actual_same_ordinal_request journal entry selected engine present running ordinal request next head
  exact ⟨⟨position, tick, selected, engine, present, ordinal, by simpa only [same] using observed⟩⟩

theorem EngineObservation.advanced {entry : EngineWriteEntry ticks pair} {reply : Option Reply}
    (source : EngineObservation entry reply) :
    ∃ final, source.tick.after.actors entry.actor = some final ∧
      final.events = source.engine.events ++ [Program.filesystemPrefixEvent (entry.request, reply)] ∧
      final.events.length = entry.engine.events.length + 1 := by
  obtain ⟨final, present, events⟩ :=
    actor_step_exact_events source.tick.operation entry.actor source.engine source.present
  rw [source.action] at events
  have exactEvents : final.events = source.engine.events ++
      [Program.filesystemPrefixEvent (entry.request, reply)] := by
    simpa only [Option.toList_some] using events
  exact ⟨final, present, exactEvents, by simp only [exactEvents, List.length_append,
    List.length_singleton, source.ordinal]⟩

-- §FS-host-boundary.caller: This one physical SDK observation updates the
-- already committed extent once, without enqueueing or changing queued bytes.
structure EngineReconciliation
    (primitive : Primitive process child native hostUid before after callers next ticks pair Token)
    (entry : EngineWriteEntry ticks pair) (reply : Option Reply) (initial : PhysicalState) where
  source : EngineObservation entry reply
  token : Token
  entered : primitive.enteredEngine token entry
  current : WriteProgress
  selected : initial.ledger entry.key = some current
  stream : State
  live : initial.stream = some stream
  final : State
  observed : primitive.observation source.position token current reply stream final

def EngineReconciliation.step
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {entry : EngineWriteEntry ticks pair} {reply : Option Reply} {initial : PhysicalState}
    (observation : EngineReconciliation primitive entry reply initial) :
    ObservedStep primitive initial
      ⟨observation.source.position, observationEvent entry.key reply, []⟩
      { stream := some observation.final
        ledger := initial.ledger.set entry.key (PrivateStreams.observed observation.current reply) } := by
  have identity := primitive.engineInput observation.token entry observation.entered
  simpa only [identity] using
    (ObservedStep.observation observation.source.position
      (Nat.le_of_lt (List.getElem?_eq_some_iff.mp observation.source.selected).1)
      observation.token observation.current initial observation.stream observation.final reply
      (by simpa only [identity] using observation.selected) observation.live observation.observed)

theorem EngineReconciliation.exact
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {entry : EngineWriteEntry ticks pair} {reply : Option Reply} {initial : PhysicalState}
    (observation : EngineReconciliation primitive entry reply initial) :
    observation.final = observation.stream ∧ observation.current.observation = .pending ∧
      (∀ response, reply = some response → nativeError response = false →
        observation.current.committed = response.1.toNat) := by
  have law := primitive.observationLaw observation.source.position observation.token observation.current reply
    observation.stream observation.final observation.observed
  exact ⟨law.2.2.1, law.2.1, law.2.2.2⟩

-- §FS-host-boundary.ownership: A positive/error return permanently disables
-- this old call. Loss is intentionally different: already pending kernel work
-- is retained and no subsequent application call is inferred from it.
theorem progress_returned_retained {initial final : PhysicalState} {event : ProgressEvent}
    {actions : List Action} (step : ProgressStep initial event actions final)
    {key : CallKey} {current : WriteProgress} {reply : Reply}
    (selected : initial.ledger key = some current) (returned : current.observation = .returned reply) :
    ∃ last, final.ledger key = some last ∧ last.input = current.input ∧
      last.committed = current.committed ∧ last.observation = .returned reply := by
  cases step with
  | begin added input fresh =>
    have different : key ≠ added := by
      intro same
      subst added
      rw [fresh] at selected
      cases selected
    exact ⟨current, by simp only [Ledger.set, ite_eq_right different]; exact selected, rfl, rfl, returned⟩
  | commit added previous stream extent stored live unreturned increase bound writable =>
    by_cases same : key = added
    · subst added
      have identity := Option.some.inj (stored.symm.trans selected)
      subst previous
      simp only [WriteProgress.canCommit, returned] at unreturned
    · exact ⟨current, by simp only [Ledger.set, ite_eq_right same]; exact selected, rfl, rfl, returned⟩
  | returned added previous response stored pending count =>
    by_cases same : key = added
    · subst added
      have identity := Option.some.inj (stored.symm.trans selected)
      subst previous
      rw [returned] at pending
      cases pending
    · exact ⟨current, by simp only [Ledger.set, ite_eq_right same]; exact selected, rfl, rfl, returned⟩
  | lost added previous stored pending =>
    by_cases same : key = added
    · subst added
      have identity := Option.some.inj (stored.symm.trans selected)
      subst previous
      rw [returned] at pending
      cases pending
    · exact ⟨current, by simp only [Ledger.set, ite_eq_right same]; exact selected, rfl, rfl, returned⟩
  | channel => exact ⟨current, selected, rfl, rfl, returned⟩

theorem ObservedJournal.returned_retained
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {position : Nat} {initial final : PhysicalState} {records : List Record}
    (history : ObservedJournal primitive position initial records final)
    {key : CallKey} {current : WriteProgress} {reply : Reply}
    (selected : initial.ledger key = some current) (returned : current.observation = .returned reply) :
    ∃ last, final.ledger key = some last ∧ last.input = current.input ∧
      last.committed = current.committed ∧ last.observation = .returned reply := by
  induction history generalizing current with
  | nil => exact ⟨current, selected, rfl, rfl, returned⟩
  | cons ordered actual tail ih =>
    obtain ⟨middle, present, input, count, returned⟩ := progress_returned_retained actual.erase selected returned
    obtain ⟨last, final, identity, amount, observed⟩ := ih present returned
    exact ⟨last, final, identity.trans input, amount.trans count, observed⟩

theorem EngineReconciliation.returned_count_forever
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {entry : EngineWriteEntry ticks pair} {reply : Reply} {initial final : PhysicalState}
    (observation : EngineReconciliation primitive entry (some reply) initial)
    (count : nativeError reply = false) {position : Nat} {records : List Record}
    (continuation : ObservedJournal primitive position
      { stream := some observation.final
        ledger := initial.ledger.set entry.key (PrivateStreams.observed observation.current (some reply)) }
      records final) :
    ∃ last, final.ledger entry.key = some last ∧ last.committed = reply.1.toNat ∧
      last.observation = .returned reply := by
  have selected : (initial.ledger.set entry.key
      (PrivateStreams.observed observation.current (some reply))) entry.key =
      some (PrivateStreams.observed observation.current (some reply)) := by simp [Ledger.set]
  obtain ⟨last, present, input, committed, returned⟩ := continuation.returned_retained selected rfl
  have exactCount := observation.exact.2.2 reply rfl count
  exact ⟨last, present, committed.trans exactCount, returned⟩

end LeanCage.Host.PrivateStreams
