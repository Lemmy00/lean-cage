import GatewayWriterSourceAdvance

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {ticks : List (ActorTick runtime)} {pair : Pair} {Token : Type}

theorem Registered.later
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {first last : Nat} {state : PhysicalState} (registered : Registered primitive first state)
    (ordered : first ≤ last) : Registered primitive last state := by
  intro key current selected
  exact (registered key current selected).monotone ordered

theorem ObservedJournal.registered_at
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {position boundary : Nat} {initial final : PhysicalState} {records : List Record}
    (journal : ObservedJournal primitive position initial records final)
    (registered : Registered primitive position initial) (ordered : position ≤ boundary)
    (bounded : ∀ record ∈ records, record.position ≤ boundary) : Registered primitive boundary final := by
  induction journal with
  | nil => exact registered.later ordered
  | cons order actual tail ih =>
    exact ih (actual.registered order registered) (bounded _ (by simp))
      (fun record member => bounded record (by simp [member]))

-- §FS-host-boundary.caller: The invariant is derived on the SAME total source
-- and physical histories. Old ACKed calls cannot make new bytes available to
-- a later source call; pending progress after loss is deliberately retained.
theorem SynchronizedJournal.source_aligned
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {initialWorld : World} {finalPopulation : Population}
    (source : ActorJournal runtime (Population.empty initialWorld) ticks finalPopulation)
    {position : Nat} {remaining : List (ActorTick runtime)} {initial final : PhysicalState} {records : List Record}
    (physical : SynchronizedJournal primitive position remaining initial records final)
    {first last : Population} (actors : ActorJournal runtime first remaining last)
    (registered : Registered primitive position initial) (aligned : SourceAligned first initial.ledger) :
    SourceAligned last final.ledger := by
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

theorem actual_acknowledged_calls_stay_closed
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {initialWorld : World} {finalPopulation : Population}
    (source : ActorJournal runtime (Population.empty initialWorld) ticks finalPopulation)
    {final : PhysicalState} {records : List Record}
    (physical : SynchronizedJournal primitive 0 ticks .unborn records final) :
    ∀ actor engine, finalPopulation.actors actor = some engine → engine.running = true →
      ∀ ordinal, ordinal < engine.events.length → ∀ current,
        final.ledger (.engine actor ordinal) = some current →
          ∃ reply, current.observation = .returned reply := by
  apply physical.source_aligned source source (registered_unborn primitive)
  intro actor engine absent
  cases absent

end LeanCage.Host.PrivateStreams
