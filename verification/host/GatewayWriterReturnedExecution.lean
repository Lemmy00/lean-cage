import GatewayWriterReturnedAdvance
import GatewayWriterSynchronizationComplete

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {ticks : List (ActorTick runtime)} {pair : Pair} {Token : Type}

-- §FS-host-boundary.caller: ACK counting remains correct through loss,
-- retirement, concurrent requests and unacknowledged kernel progress.
theorem SynchronizedJournal.returned_aligned
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {initialWorld : World} {finalPopulation : Population}
    (source : ActorJournal runtime (Population.empty initialWorld) ticks finalPopulation)
    {position : Nat} {remaining : List (ActorTick runtime)} {initial final : PhysicalState} {records : List Record}
    (physical : SynchronizedJournal primitive position remaining initial records final)
    {first last : Population} (actors : ActorJournal runtime first remaining last)
    (registered : Registered primitive position initial) (aligned : ReturnedSourceAligned first initial.ledger) :
    ReturnedSourceAligned last final.ledger := by
  induction physical generalizing first with
  | nil => cases actors; exact aligned
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
      exact ih actorTail nextRegistered afterRow

theorem returned_ordinal_monotone {first last : List Program.Event} (ordered : first <+: last) :
    returnedOrdinal first ≤ returnedOrdinal last := by
  obtain ⟨rest, rfl⟩ := ordered
  rw [returned_ordinal_append]
  omega

theorem registered_actor_returned_bound
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {initialWorld : World} {finalPopulation : Population}
    (journal : ActorJournal runtime (Population.empty initialWorld) ticks finalPopulation)
    {position : Nat} {tick : ActorTick runtime} (selectedTick : ticks[position]? = some tick)
    (state : PhysicalState) (registered : Registered primitive position state)
    (actor ordinal : Nat) (current : WriteProgress) (stored : state.ledger (.engine actor ordinal) = some current) :
    ∃ engine, tick.before.actors actor = some engine ∧ ordinal ≤ returnedOrdinal engine.events := by
  obtain ⟨entry, token, entered, key, input, order⟩ := registered_engine_source registered actor ordinal current stored
  have fields := CallKey.engine.inj key
  obtain ⟨leading, inside, trailing, shape, interval⟩ :=
    journal_between_selected journal entry.selected selectedTick order
  obtain ⟨engine, present, eventPrefix⟩ := actor_journal_keeps_actor interval entry.actor entry.engine entry.present
  have sourceCount := actual_running_returned_ordinal journal entry.selected entry.actor entry.engine entry.present entry.running
  refine ⟨engine, by simpa only [fields.1] using present, ?_⟩
  rw [← fields.2, ← sourceCount]
  exact returned_ordinal_monotone eventPrefix

-- §AR-host-boundary.primitives: Every actual engine commit uses its CURRENT
-- returned-call cursor. The last lost call retains that same cursor, while
-- an acknowledged older call cannot enqueue a second copy.
theorem actual_engine_commit_cursor
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {initialWorld : World} {finalPopulation : Population}
    (journal : ActorJournal runtime (Population.empty initialWorld) ticks finalPopulation)
    {position : Nat} {tick : ActorTick runtime} (selectedTick : ticks[position]? = some tick)
    (state : PhysicalState) (registered : Registered primitive position state)
    (aligned : ReturnedSourceAligned tick.before state.ledger)
    (token : Token) (current : WriteProgress) (first last : State) (extent : Nat)
    (stored : state.ledger (primitive.input token).1 = some current)
    (progress : primitive.progress position token current extent first last)
    (actor ordinal : Nat) (key : (primitive.input token).1 = .engine actor ordinal) :
    ∃ engine, tick.before.actors actor = some engine ∧ ordinal = returnedOrdinal engine.events := by
  have selected : state.ledger (.engine actor ordinal) = some current := by simpa only [key] using stored
  obtain ⟨engine, present, bounded⟩ := registered_actor_returned_bound journal selectedTick state registered actor ordinal current selected
  refine ⟨engine, present, ?_⟩
  by_cases older : ordinal < returnedOrdinal engine.events
  · obtain ⟨reply, returned⟩ := aligned actor engine present ordinal older current selected
    have writable := (primitive.progressLaw _ _ _ _ _ _ progress).2.1
    simp only [WriteProgress.canCommit, returned] at writable
  · omega

theorem actual_engine_commit_cursors_ordered
    {initialWorld : World} {finalPopulation : Population}
    (journal : ActorJournal runtime (Population.empty initialWorld) ticks finalPopulation)
    {first last : Nat} {beforeTick afterTick : ActorTick runtime}
    (beforeSelected : ticks[first]? = some beforeTick) (afterSelected : ticks[last]? = some afterTick)
    (ordered : first ≤ last) (actor : ActorId) (beforeEngine afterEngine : EngineState)
    (beforePresent : beforeTick.before.actors actor = some beforeEngine)
    (afterPresent : afterTick.before.actors actor = some afterEngine) :
    returnedOrdinal beforeEngine.events ≤ returnedOrdinal afterEngine.events :=
  returned_ordinal_monotone (selected_events_prefix journal ordered beforeSelected afterSelected actor beforeEngine afterEngine
    beforePresent afterPresent)

end LeanCage.Host.PrivateStreams
