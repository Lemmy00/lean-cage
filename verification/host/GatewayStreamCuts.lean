import GatewayStreamSynchronization

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {ticks : List (ActorTick runtime)} {pair : Pair} {Token : Type}

-- §FS-host-boundary.caller: A cut stores the very row of the supplied queue
-- journal, with its real pending effects, mandatory ACK and both continuations.
structure SynchronizedCut
    (primitive : Primitive process child native hostUid before after callers next ticks pair Token)
    (start position : Nat) (initial final : PhysicalState) (records : List Record) where
  tick : ActorTick runtime
  selected : ticks[position]? = some tick
  beforeBatch : PhysicalState
  pending : PhysicalState
  acknowledged : PhysicalState
  leading : List Record
  progress : List Record
  replies : List Record
  trailing : List Record
  prefixRun : ObservedJournal primitive start initial leading beforeBatch
  batch : PendingBatch primitive position beforeBatch pending progress
  row : EngineRow primitive position tick pending replies acknowledged
  suffixRun : ObservedJournal primitive (position + 1) acknowledged trailing final
  shape : records = leading ++ progress ++ replies ++ trailing

theorem SynchronizedJournal.cut
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {position : Nat} {remaining : List (ActorTick runtime)}
    {initial final : PhysicalState} {records : List Record}
    (journal : SynchronizedJournal primitive position remaining initial records final)
    (index : Nat) (inside : index < remaining.length) :
    Nonempty (SynchronizedCut primitive position (position + index) initial final records) := by
  induction journal generalizing index with
  | nil => simp only [List.length_nil] at inside; omega
  | @cons position tick remaining initial pending acknowledged final progress replies rest selected batch row tail ih =>
    cases index with
    | zero =>
      exact ⟨⟨tick, by simpa only [Nat.add_zero] using selected, initial, pending, acknowledged,
        [], progress, replies, rest, .nil _ _, batch, row, tail.erase, by simp⟩⟩
    | succ index =>
      obtain ⟨cut⟩ := ih index (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using inside)
      have boundary : position + 1 + index = position + (index + 1) := by omega
      let head : ObservedJournal primitive position initial (progress ++ replies) acknowledged := by
        exact batch.actual.append_at (Nat.le_refl _) (fun record member => by
          rw [batch.positions record member]; exact Nat.le_refl _) row.run
      have headPositions : ∀ record ∈ progress ++ replies, record.position ≤ position + 1 := by
        intro record member
        rcases List.mem_append.mp member with member | member
        · rw [batch.positions record member]; omega
        · rw [row.positions record member]; omega
      let prefixRun := head.append_at (by omega) headPositions cut.prefixRun
      refine ⟨⟨cut.tick, ?_, cut.beforeBatch, cut.pending, cut.acknowledged,
        (progress ++ replies) ++ cut.leading, cut.progress, cut.replies, cut.trailing,
        prefixRun, ?_, ?_, ?_, ?_⟩⟩
      · simpa only [boundary] using cut.selected
      · simpa only [boundary] using cut.batch
      · simpa only [boundary] using cut.row
      · simpa only [boundary] using cut.suffixRun
      · simp only [cut.shape, List.append_assoc]

end LeanCage.Host.PrivateStreams
