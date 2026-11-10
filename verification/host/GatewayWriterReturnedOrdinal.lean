import GatewayWriterActorAlignment

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

def returnedOrdinal : List Program.Event → Nat
  | [] => 0
  | .returned _ _ :: rest => returnedOrdinal rest + 1
  | .lost _ :: rest => returnedOrdinal rest

theorem returned_ordinal_append (first last : List Program.Event) :
    returnedOrdinal (first ++ last) = returnedOrdinal first + returnedOrdinal last := by
  induction first with
  | nil => simp [returnedOrdinal]
  | cons event rest ih => cases event <;> simp [returnedOrdinal, ih, Nat.add_comm, Nat.add_left_comm]

theorem returned_ordinal_le (events : List Program.Event) : returnedOrdinal events ≤ events.length := by
  induction events with
  | nil => exact Nat.le_refl _
  | cons event rest ih => cases event <;> simp only [returnedOrdinal, List.length_cons] <;> omega

theorem residual_returned_ordinal {α : Type} {first last : Program α} {events : List Program.Event}
    (source : Residual first events last) : returnedOrdinal events = events.length := by
  induction source with
  | refl => rfl
  | call tail ih => simpa [returnedOrdinal] using ih

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {ticks : List (ActorTick runtime)} {pair : Pair} {Token : Type}

theorem actual_running_returned_ordinal {initialWorld : World} {finalPopulation : Population}
    (journal : ActorJournal runtime (Population.empty initialWorld) ticks finalPopulation)
    {position : Nat} {tick : ActorTick runtime} (selectedTick : ticks[position]? = some tick)
    (actor : ActorId) (engine : EngineState) (present : tick.before.actors actor = some engine)
    (running : engine.running = true) : returnedOrdinal engine.events = engine.events.length := by
  obtain ⟨leading, trailing, length, shape⟩ := selected_tick_exact_split selectedTick
  exact residual_returned_ordinal (selected_actor_head_for journal leading trailing tick shape present running)

-- §FS-host-boundary.ownership: A lost source event does not count as a
-- returned call. This cursor therefore retains its pending kernel extent
-- through loss and later process retirement, rather than inventing an ACK.
def ReturnedSourceAligned (population : Population) (ledger : Ledger) : Prop :=
  ∀ actor engine, population.actors actor = some engine →
    OlderReturned actor (returnedOrdinal engine.events) ledger

theorem PendingBatch.older_returned_bounded
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {position : Nat} {initial final : PhysicalState} {records : List Record}
    (batch : PendingBatch primitive position initial final records)
    (tick : ActorTick runtime) (selectedTick : ticks[position]? = some tick)
    (actor : ActorId) (engine : EngineState) (present : tick.before.actors actor = some engine)
    (ordinal : Nat) (bounded : ordinal ≤ engine.events.length)
    (before : OlderReturned actor ordinal initial.ledger) : OlderReturned actor ordinal final.ledger := by
  apply batch.actual.older_returned actor ordinal before
  intro record member added input event
  have selected : ticks[record.position]? = some tick := by rw [batch.positions record member]; exact selectedTick
  have noOldBirth : ∀ {first last : PhysicalState},
      ObservedStep primitive first record last → ordinal ≤ added := by
    intro first last actual
    obtain ⟨original, source, count⟩ := actual.engine_entry_ordinal tick selected actor added input event
    have same := Option.some.inj (source.symm.trans present)
    subst original
    omega
  have occurs : ∃ first last, Nonempty (ObservedStep primitive first record last) := by
    have history := batch.actual
    clear before batch selectedTick present event selected noOldBirth
    induction history with
    | nil => cases member
    | cons order actual tail ih =>
      rcases List.mem_cons.mp member with same | later
      · subst record; exact ⟨_, _, ⟨actual⟩⟩
      · exact ih later
  obtain ⟨first, last, ⟨actual⟩⟩ := occurs
  exact noOldBirth actual

theorem ReturnedSourceAligned.pending
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {position : Nat} {tick : ActorTick runtime} {initial final : PhysicalState} {records : List Record}
    (selectedTick : ticks[position]? = some tick)
    (batch : PendingBatch primitive position initial final records)
    (aligned : ReturnedSourceAligned tick.before initial.ledger) : ReturnedSourceAligned tick.before final.ledger := by
  intro actor engine present
  exact batch.older_returned_bounded tick selectedTick actor engine present _ (returned_ordinal_le engine.events)
    (aligned actor engine present)

end LeanCage.Host.PrivateStreams
