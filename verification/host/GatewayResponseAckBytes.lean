import GatewayResponseAckSources
import GatewayStreamCuts
import GatewayStreamKeyAccounting

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {ticks : List (ActorTick runtime)} {pair : Pair} {Token : Type}

-- §FS-host-boundary.caller: The mandatory row reconciles this exact source
-- call. Its successful ACK fixes every partial commit in the whole history;
-- later loss or teardown cannot reopen the acknowledged call.
theorem SynchronizedJournal.actual_ack_bytes
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {final : PhysicalState} {records : List Record}
    (physical : SynchronizedJournal primitive 0 ticks .unborn records final)
    (entry : EngineWriteEntry ticks pair) (reply : Reply)
    (observed : EngineWriteObservation entry (some reply)) (success : nativeError reply = false) :
    ∃ current, final.ledger entry.key = some current ∧
      current.committed = reply.1.toNat ∧ current.observation = .returned reply ∧
      records.flatMap (Record.bytesFor entry.key) = entry.request.left.data.toList.take reply.1.toNat := by
  obtain ⟨cut⟩ := physical.cut entry.position (List.getElem?_eq_some_iff.mp entry.selected).1
  have cutSelected : ticks[entry.position]? = some cut.tick := by simpa only [Nat.zero_add] using cut.selected
  have sameTick := Option.some.inj (cutSelected.symm.trans entry.selected)
  have scan := write_observation_complete entry.tick entry.actor entry.engine entry.present
    entry.request (some reply) entry.writing observed.action
  have scanned : writeObservationAt cut.tick = some ⟨entry.actor, entry.engine.events.length, entry.request, some reply⟩ := by
    rw [sameTick]; exact scan
  obtain ⟨source, actor, ordinal, request, ack, position, tick, stored⟩ := cut.row.private_ack _ scanned entry.engine
    (by simpa only [sameTick] using entry.present) entry.handle entry.input
    (by rw [entry.endpoint]; cases sender : entry.sender <;> simp [Pair.endpoint])
  have key : source.key = entry.key := by simp only [EngineWriteEntry.key, actor, ordinal]
  have selected : cut.acknowledged.ledger entry.key = some (PrivateStreams.observed ack.current (some reply)) := stored
  obtain ⟨current, present, input, committed, returned⟩ := cut.suffixRun.returned_retained selected rfl
  have exactCount := ack.exact.2.2 reply rfl success
  have count : current.committed = reply.1.toNat := committed.trans exactCount
  have sourceInput := (primitive.observationLaw _ _ _ _ _ _ ack.observed).1
  rw [primitive.engineInput ack.token source ack.entered] at sourceInput
  have bytes : current.input.bytes = entry.request.left.data.toList := by
    simpa only [PrivateStreams.observed, EngineWriteEntry.description, request] using
      congrArg (fun value : WriteDescription => value.bytes) (input.trans sourceInput)
  exact ⟨current, present, count, returned, by
    simpa only [bytes, count] using actual_key_committed_prefix physical.erase entry.key current present⟩

-- §FS-host-boundary.caller: Every earlier writer ACK selects its actual
-- global call key and exact once-only committed payload, not a guessed count.
theorem actual_response_ack_key_bytes
    (descriptors : DescriptorContract kernel) (directories : DirectoryRetirementContract kernel)
    (sdk : RuntimeDescriptorContract runtime) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (environment : InterferenceContract kernel)
    {initialWorld : World} {population : Population}
    (source : ActorJournal runtime (Population.empty initialWorld) ticks population)
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {final : PhysicalState} {records : List Record}
    (physical : SynchronizedJournal primitive 0 ticks .unborn records final)
    (last : EngineWriteEntry ticks pair) (response : EngineResponse last)
    (history : SelectedActorHistory runtime initialWorld ticks last.tick last.actor last.engine)
    (handle : Handle) (inherited : history.launch.references 1 = some handle)
    (endpoint : handle.object = pair.engine)
    (index : Nat) (event : Request × Reply)
    (selected : response.source.writer.acknowledged[index]? = some event) :
    records.flatMap (Record.bytesFor (.engine last.actor
      (last.engine.events.length - response.source.writer.acknowledged.length + index))) =
        event.1.left.data.toList.take event.2.1.toNat := by
  obtain ⟨entry, actor, request, held, sender, observed, position, ordinal⟩ :=
    actual_response_ack_source_indexed descriptors directories sdk lifetimes references environment
      source last response history handle inherited endpoint index event selected
  have success := (acknowledged_source_reply response.source.writer.progress index event selected).1
  obtain ⟨current, stored, count, returned, bytes⟩ := physical.actual_ack_bytes entry event.2 observed success
  simpa only [EngineWriteEntry.key, actor, ordinal, request] using bytes

private theorem flatMap_congr_on {α β : Type} (items : List α) (first last : α → List β)
    (same : ∀ item ∈ items, first item = last item) : items.flatMap first = items.flatMap last := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.flatMap_cons, same head (by simp)]
    rw [ih (fun item member => same item (by simp [member]))]

private theorem acknowledged_bytes_list (events : List (Request × Reply)) :
    events.flatMap (fun event => event.1.left.data.toList.take event.2.1.toNat) =
      (EntrypointWriterPrefix.acknowledgedBytes events).data.toList := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
    simp only [List.flatMap_cons, EntrypointWriterPrefix.acknowledgedBytes,
      ByteArray.toList_data_append, ByteArray.data_extract, Array.toList_extract,
      List.extract, Nat.sub_zero, List.drop_zero, ih]

-- §FS-host-boundary.caller: Grouping actual source keys in writer order now
-- reconstructs the complete acknowledged response prefix. Queue-order and
-- caller-read authority are retained as separate source obligations.
theorem actual_response_ack_grouped_prefix
    (descriptors : DescriptorContract kernel) (directories : DirectoryRetirementContract kernel)
    (sdk : RuntimeDescriptorContract runtime) (lifetimes : LifetimeContract runtime)
    (references : ReferenceContract runtime) (environment : InterferenceContract kernel)
    {initialWorld : World} {population : Population}
    (source : ActorJournal runtime (Population.empty initialWorld) ticks population)
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {final : PhysicalState} {records : List Record}
    (physical : SynchronizedJournal primitive 0 ticks .unborn records final)
    (last : EngineWriteEntry ticks pair) (response : EngineResponse last)
    (history : SelectedActorHistory runtime initialWorld ticks last.tick last.actor last.engine)
    (handle : Handle) (inherited : history.launch.references 1 = some handle)
    (endpoint : handle.object = pair.engine) :
    response.source.writer.acknowledged.zipIdx.flatMap (fun item =>
      records.flatMap (Record.bytesFor (.engine last.actor
        (last.engine.events.length - response.source.writer.acknowledged.length + item.2)))) =
      (response.source.context.bytes.extract 0 response.source.writer.offset).data.toList := by
  have perKey := flatMap_congr_on response.source.writer.acknowledged.zipIdx
    (fun item => records.flatMap (Record.bytesFor (.engine last.actor
      (last.engine.events.length - response.source.writer.acknowledged.length + item.2))))
    (fun item => item.1.1.left.data.toList.take item.1.2.1.toNat) (by
      intro item member
      exact actual_response_ack_key_bytes descriptors directories sdk lifetimes references environment
        source physical last response history handle inherited endpoint item.2 item.1
          (List.mem_zipIdx_iff_getElem?.mp member))
  rw [perKey]
  have projected := List.flatMap_map (Prod.fst : (Request × Reply) × Nat → Request × Reply)
    (fun event => event.1.left.data.toList.take event.2.1.toNat) response.source.writer.acknowledged.zipIdx
  rw [List.zipIdx_map_fst] at projected
  rw [← projected, acknowledged_bytes_list, response.payload.2.2.2.2]

end LeanCage.Host.PrivateStreams
