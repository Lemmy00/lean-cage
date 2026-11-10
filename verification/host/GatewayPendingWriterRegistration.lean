import GatewayWriterRowProducer
import GatewayResponseAckSources

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {ticks : List (ActorTick runtime)} {pair : Pair} {Token : Type}

structure PendingWriterRegistration
    (primitive : Primitive process child native hostUid before after callers next ticks pair Token)
    (entry : EngineWriteEntry ticks pair) (initial : PhysicalState) where
  final : PhysicalState
  records : List Record
  batch : PendingBatch primitive entry.position initial final records
  registered : final.ledger entry.key ≠ none

-- §FS-host-boundary.caller: The actual pending head is registered before
-- peer progress, even at a native recv/retire row. It does not inspect an ACK
-- scanner or wait for the writer to return or copy out a successful count.
theorem actual_pending_writer_registration
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    (tokens : EngineTokens primitive) (entry : EngineWriteEntry ticks pair) (initial : PhysicalState) :
    Nonempty (PendingWriterRegistration primitive entry initial) := by
  classical
  cases stored : initial.ledger entry.key with
  | some current => exact ⟨⟨initial, [], ⟨.nil _ _, by simp, by simp⟩, by rw [stored]; simp⟩⟩
  | none =>
    let final : PhysicalState :=
      { initial with ledger := initial.ledger.set entry.key ⟨entry.description, 0, Nat.zero_le _, .pending⟩ }
    exact ⟨⟨final, [⟨entry.position, .begin entry.key entry.description, []⟩],
      ⟨.cons (Nat.le_refl _) (.engine initial entry (tokens.token entry) (tokens.entered entry) stored) (.nil _ _),
        by intro record member; cases List.mem_singleton.mp member; rfl,
        by intro record member; cases List.mem_singleton.mp member; trivial⟩,
      by simp [final, Ledger.set]⟩⟩

-- §AR-host-boundary.interfaces.gateway: The per-call kernel observer supplies
-- only its actual current source head and raw fd1 operand. Source history and
-- the real handoff derive the current endpoint/OFD and pure registration.
theorem actual_inherited_pending_writer
    (descriptors : DescriptorContract kernel) (directories : DirectoryRetirementContract kernel)
    (sdk : RuntimeDescriptorContract runtime)
    {initialWorld : World} {population : Population}
    (source : ActorJournal runtime (Population.empty initialWorld) ticks population)
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    (tokens : EngineTokens primitive) {position : Nat} {tick : ActorTick runtime}
    (selected : ticks[position]? = some tick) (actor : ActorId) (engine : EngineState)
    (present : tick.before.actors actor = some engine) (running : engine.running = true)
    (history : SelectedActorHistory runtime initialWorld ticks tick actor engine)
    (handle : Handle) (inherited : history.launch.references 1 = some handle)
    (endpoint : handle.object = pair.engine) (request : Request) (next : Reply → Program UInt32)
    (head : engine.current = .call (.filesystem request) next) (writing : request.op = .write)
    (fd : request.first = 1) (initial : PhysicalState) :
    ∃ entry : EngineWriteEntry ticks pair, entry.position = position ∧ entry.actor = actor ∧ entry.request = request ∧
      Nonempty (PendingWriterRegistration primitive entry initial) := by
  have live := actual_live_inherited_reference descriptors directories sdk source history present running inherited
  let entry : EngineWriteEntry ticks pair := {
    position, tick, selected, actor, engine, present, running, request, next, head, writing,
    sender := .engine, handle, input := by simpa only [fd] using live, endpoint }
  exact ⟨entry, rfl, rfl, rfl, actual_pending_writer_registration tokens entry initial⟩

theorem PendingWriterRegistration.retained
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {entry : EngineWriteEntry ticks pair} {initial : PhysicalState}
    (registration : PendingWriterRegistration primitive entry initial)
    {position : Nat} {records : List Record} {final : PhysicalState}
    (after : ObservedJournal primitive position registration.final records final) :
    final.ledger entry.key ≠ none := by
  cases stored : registration.final.ledger entry.key with
  | none => exact False.elim (registration.registered stored)
  | some current =>
    obtain ⟨last, present, input, increase, bytes⟩ := after.key_bytes entry.key current stored
    rw [present]
    simp

-- Current-head registration and the mandatory observation scanner are both
-- before kernel progress. Combining them cannot delete or duplicate an entry.
theorem actual_pending_and_ack_registration
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    (tokens : EngineTokens primitive) (entry : EngineWriteEntry ticks pair) (initial : PhysicalState) :
    ∃ registration : EngineRegistration primitive entry.position entry.tick initial,
      registration.final.ledger entry.key ≠ none := by
  obtain ⟨pending⟩ := actual_pending_writer_registration tokens entry initial
  obtain ⟨ack⟩ := actual_engine_registration tokens entry.selected pending.final
  let registration : EngineRegistration primitive entry.position entry.tick initial := {
    final := ack.final
    records := pending.records ++ ack.records
    actual := pending.batch.actual.append_at (Nat.le_refl _) (fun record member => by
      rw [pending.batch.positions record member]; exact Nat.le_refl _) ack.actual
    positions := by
      intro record member
      rcases List.mem_append.mp member with first | last
      · exact pending.batch.positions record first
      · exact ack.positions record last
    pending := by
      intro record member
      rcases List.mem_append.mp member with first | last
      · exact pending.batch.unobserved record first
      · exact ack.pending record last
    outside := ack.outside }
  exact ⟨registration, pending.retained ack.actual⟩

end LeanCage.Host.PrivateStreams
