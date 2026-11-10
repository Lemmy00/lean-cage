import GatewayWriterSynchronization

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {ticks : List (ActorTick runtime)} {pair : Pair} {Token : Type}

-- §AR-host-boundary.primitives: Pending kernel progress may precede an ACK,
-- including commits whose source will be lost. Engine ACKs are consumed only
-- by the exhaustive source-row synchronizer, never silently inside this batch.
def pendingRecord (record : Record) : Prop :=
  match record.event with
  | .returned (.engine _ _) _ | .lost (.engine _ _) => False
  | _ => True

structure PendingBatch
    (primitive : Primitive process child native hostUid before after callers next ticks pair Token)
    (position : Nat) (initial final : PhysicalState) (records : List Record) where
  actual : ObservedJournal primitive position initial records final
  positions : ∀ record ∈ records, record.position = position
  unobserved : ∀ record ∈ records, pendingRecord record

noncomputable def ObservedJournal.earlier
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {first last : Nat} {initial final : PhysicalState} {records : List Record}
    (ordered : first ≤ last) (actual : ObservedJournal primitive last initial records final) :
    ObservedJournal primitive first initial records final := by
  cases actual with
  | nil => exact .nil _ _
  | cons order actual tail => exact .cons (Nat.le_trans ordered order) actual tail

noncomputable def ObservedJournal.append_at
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {position boundary : Nat} {initial middle final : PhysicalState} {records suffix : List Record}
    (actual : ObservedJournal primitive position initial records middle)
    (ordered : position ≤ boundary) (bounded : ∀ record ∈ records, record.position ≤ boundary)
    (tail : ObservedJournal primitive boundary middle suffix final) :
    ObservedJournal primitive position initial (records ++ suffix) final := by
  induction actual with
  | nil => exact tail.earlier ordered
  | @cons position initial next middle record records order step remaining ih =>
    exact .cons order step (ih (bounded record (by simp))
      (fun selected member => bounded selected (by simp [member])) tail)

-- §FS-host-boundary.caller: This follows EVERY supplied global row in order.
-- Each row's pending effects are followed by its actual mandatory ACK/loss;
-- later rows therefore cannot keep committing an already acknowledged call.
inductive SynchronizedJournal
    (primitive : Primitive process child native hostUid before after callers next ticks pair Token) :
    Nat → List (ActorTick runtime) → PhysicalState → List Record → PhysicalState → Type 1 where
  | nil (position : Nat) (state : PhysicalState) : SynchronizedJournal primitive position [] state [] state
  | cons {position : Nat} {tick : ActorTick runtime} {remaining : List (ActorTick runtime)}
      {initial pending acknowledged final : PhysicalState} {progress replies rest : List Record}
      (selected : ticks[position]? = some tick)
      (batch : PendingBatch primitive position initial pending progress)
      (row : EngineRow primitive position tick pending replies acknowledged)
      (tail : SynchronizedJournal primitive (position + 1) remaining acknowledged rest final) :
      SynchronizedJournal primitive position (tick :: remaining) initial (progress ++ replies ++ rest) final

noncomputable def SynchronizedJournal.erase
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {position : Nat} {remaining : List (ActorTick runtime)} {initial final : PhysicalState} {records : List Record}
    (journal : SynchronizedJournal primitive position remaining initial records final) :
    ObservedJournal primitive position initial records final := by
  induction journal with
  | nil => exact .nil _ _
  | @cons position tick remaining initial pending acknowledged final progress replies rest selected batch row tail ih =>
    have replySuffix := row.run.append_at (by omega)
      (fun record member => by rw [row.positions record member]; omega) ih
    simpa only [List.append_assoc] using batch.actual.append_at (Nat.le_refl _)
      (fun record member => by rw [batch.positions record member]; exact Nat.le_refl _) replySuffix

-- A row's exact registered key is reconciled even if the call's captured
-- descriptor was closed or reused later. Queue bytes are unchanged by the ACK.
theorem synchronized_registered_observation
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {position : Nat} {tick : ActorTick runtime} {initial final : PhysicalState} {records : List Record}
    (row : EngineRow primitive position tick initial records final)
    (observation : WriteObservation) (actual : writeObservationAt tick = some observation)
    (current : WriteProgress) (registered : initial.ledger observation.key = some current) :
    final.stream = initial.stream ∧ ∃ last, final.ledger observation.key = some last ∧
      last.input = current.input ∧ last.committed = current.committed ∧
      last.observation = replyObservation observation.reply :=
  ⟨row.queue_unchanged, row.covers observation actual current registered⟩

end LeanCage.Host.PrivateStreams
