import GatewayStreamReadRows

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {ticks : List (ActorTick runtime)} {pair : Pair} {Token : Type}

theorem NativeReadRow.positions
    {journal : NativeExternalJournal process child native hostUid before callers ticks after next}
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {position : Nat} {initial final : PhysicalState} {records : List Record}
    (row : NativeReadRow journal primitive position initial records final) :
    ∀ record ∈ records, record.position = position := by
  cases row with
  | outside => simp
  | received => intro record member; cases List.mem_singleton.mp member; rfl

theorem NativeReadRow.pending
    {journal : NativeExternalJournal process child native hostUid before callers ticks after next}
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {position : Nat} {initial final : PhysicalState} {records : List Record}
    (row : NativeReadRow journal primitive position initial records final) :
    ∀ record ∈ records, pendingRecord record := by
  cases row with
  | outside => simp
  | received => intro record member; cases List.mem_singleton.mp member; trivial

noncomputable def nativeCallerBytesAt
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    (position : Nat) : Bytes :=
  match nativeReadAt (pair := pair) journal position with
  | none => []
  | some entry => if entry.receiver = .caller then entry.bytes.data.toList else []

theorem NativeReadRow.caller_bytes
    {journal : NativeExternalJournal process child native hostUid before callers ticks after next}
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {position : Nat} {initial final : PhysicalState} {records : List Record}
    (row : NativeReadRow journal primitive position initial records final) :
    (records.flatMap Record.actions).flatMap (PrivateStreams.received .caller) = nativeCallerBytesAt (pair := pair) journal position := by
  cases row with
  | outside none => simp only [List.flatMap_nil, nativeCallerBytesAt, none]
  | received entry selected flags before final live actual =>
    simp only [nativeCallerBytesAt, selected, PrivateStreams.received, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]

-- §FS-host-boundary.caller: Pending kernel progress cannot hide a caller
-- receive. Every actual stored native receive is processed exactly once, then
-- the same global row's mandatory ACK/loss advances the source ledger.
inductive ChannelJournal
    (journal : NativeExternalJournal process child native hostUid before callers ticks after next)
    (primitive : Primitive process child native hostUid before after callers next ticks pair Token) :
    Nat → List (ActorTick runtime) → PhysicalState → List Record → PhysicalState → Type 1 where
  | nil (position : Nat) (state : PhysicalState) : ChannelJournal journal primitive position [] state [] state
  | cons {position : Nat} {tick : ActorTick runtime} {remaining : List (ActorTick runtime)}
      {initial pending read acknowledged final : PhysicalState} {progress readings replies rest : List Record}
      (selected : ticks[position]? = some tick)
      (batch : PendingBatch primitive position initial pending progress)
      (otherReads : ∀ record ∈ progress, ∀ bytes, Action.read .caller bytes ∉ record.actions)
      (reader : NativeReadRow journal primitive position pending readings read)
      (row : EngineRow primitive position tick read replies acknowledged)
      (tail : ChannelJournal journal primitive (position + 1) remaining acknowledged rest final) :
      ChannelJournal journal primitive position (tick :: remaining) initial
        (progress ++ readings ++ replies ++ rest) final

noncomputable def ChannelJournal.erase
    {journal : NativeExternalJournal process child native hostUid before callers ticks after next}
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {position : Nat} {remaining : List (ActorTick runtime)}
    {initial final : PhysicalState} {records : List Record}
    (physical : ChannelJournal journal primitive position remaining initial records final) :
    SynchronizedJournal primitive position remaining initial records final := by
  induction physical with
  | nil => exact .nil _ _
  | cons selected batch otherReads reader row tail ih =>
    let joined : PendingBatch primitive _ _ _ _ := {
      actual := batch.actual.append_at (Nat.le_refl _) (fun record member => by
        rw [batch.positions record member]; exact Nat.le_refl _) (reader.erase journal)
      positions := by
        intro record member
        rcases List.mem_append.mp member with first | last
        · exact batch.positions record first
        · exact reader.positions record last
      unobserved := by
        intro record member
        rcases List.mem_append.mp member with first | last
        · exact batch.unobserved record first
        · exact reader.pending record last }
    simpa only [List.append_assoc] using SynchronizedJournal.cons selected joined row ih

private theorem other_caller_reads_empty (records : List Record)
    (excluded : ∀ record ∈ records, ∀ bytes, Action.read .caller bytes ∉ record.actions) :
    (records.flatMap Record.actions).flatMap (PrivateStreams.received .caller) = [] := by
  simp only [List.flatMap_eq_nil_iff]
  intro action member
  obtain ⟨record, belongs, inside⟩ := List.mem_flatMap.mp member
  cases action <;> try rfl
  next receiver bytes =>
    cases receiver with
    | caller => exact False.elim (excluded record belongs bytes inside)
    | engine => rfl

theorem EngineRow.no_received_bytes
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {position : Nat} {tick : ActorTick runtime} {initial final : PhysicalState} {records : List Record}
    (row : EngineRow primitive position tick initial records final) :
    (records.flatMap Record.actions).flatMap (PrivateStreams.received .caller) = [] := by
  cases row with
  | absent | outside => rfl
  | acknowledged => rfl

-- §AR-host-boundary.interfaces.gateway: The received byte projection is now
-- the unique stored-call projection of this exact global journal. The separate
-- source-use producer must identify these rows with the original C receive run.
theorem ChannelJournal.caller_bytes
    {journal : NativeExternalJournal process child native hostUid before callers ticks after next}
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {position : Nat} {remaining : List (ActorTick runtime)}
    {initial final : PhysicalState} {records : List Record}
    (physical : ChannelJournal journal primitive position remaining initial records final) :
    (records.flatMap Record.actions).flatMap (PrivateStreams.received .caller) =
      (List.range' position remaining.length).flatMap (nativeCallerBytesAt (pair := pair) journal) := by
  induction physical with
  | nil => rfl
  | cons selected batch otherReads reader row tail ih =>
    simp only [List.length_cons, List.range'_succ, List.flatMap_cons,
      List.flatMap_append, reader.caller_bytes, row.no_received_bytes, ih,
      other_caller_reads_empty _ otherReads, List.nil_append, List.append_nil]

end LeanCage.Host.PrivateStreams
