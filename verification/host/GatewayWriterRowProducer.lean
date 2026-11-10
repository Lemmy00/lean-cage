import GatewayStreamSourceRegistration

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {ticks : List (ActorTick runtime)} {pair : Pair} {Token : Type}

-- §FS-host-boundary.caller: Source registration supplies the exhaustive
-- coverage test. The only remaining row input is the physical observation of
-- this individual actual SDK write/loss, with its already committed count.
theorem actual_registered_engine_row
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {initialWorld : World} {finalPopulation : Population}
    (journal : ActorJournal runtime (Population.empty initialWorld) ticks finalPopulation)
    {position : Nat} {tick : ActorTick runtime} (selected : ticks[position]? = some tick)
    {initial : PhysicalState} (registered : Registered primitive position initial)
    (registration : EngineRegistration primitive position tick initial)
    {ready : PhysicalState} {records : List Record}
    (pending : PendingBatch primitive position registration.final ready records)
    (observation : ∀ (entry : EngineWriteEntry ticks pair) reply,
      writeObservationAt tick = some ⟨entry.actor, entry.engine.events.length, entry.request, reply⟩ →
      ready.ledger entry.key ≠ none → Nonempty (EngineAckSample primitive position entry reply ready)) :
    ∃ replies final, Nonempty (EngineRow primitive position tick ready replies final) := by
  have afterRegistration : Registered primitive position registration.final :=
    registration.actual.registered_at registered (Nat.le_refl _)
      (fun record member => by rw [registration.positions record member]; exact Nat.le_refl _)
  have afterPending : Registered primitive position ready :=
    pending.actual.registered_at afterRegistration (Nat.le_refl _)
      (fun record member => by rw [pending.positions record member]; exact Nat.le_refl _)
  exact actual_engine_row journal position tick selected ready afterPending
    ⟨registration.outside_after pending.actual, observation⟩

end LeanCage.Host.PrivateStreams
