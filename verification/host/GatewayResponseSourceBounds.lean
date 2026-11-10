import GatewayChannelWriteSources

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

-- §FS-host-boundary.caller: A response's raw prelude is unique on the same
-- actual source prefix. Counting ACKs therefore identifies source keys rather
-- than merely bounding their offsets.
theorem pending_response_base_unique {firstEngine lastEngine : EngineState} {firstRequest lastRequest : Request}
    (first : EntrypointWriterPrefix.PendingCut firstEngine firstRequest)
    (last : EntrypointWriterPrefix.PendingCut lastEngine lastRequest)
    (before : EntrypointWriterPrefix.ResponseFrontier first.occurrence.logicalBefore firstRequest none)
    (after : EntrypointWriterPrefix.ResponseFrontier last.occurrence.logicalBefore lastRequest none)
    (ordered : firstEngine.events <+: lastEngine.events) :
    firstEngine.events.length - before.writer.acknowledged.length =
      lastEngine.events.length - after.writer.acknowledged.length := by
  obtain ⟨left, firstPrelude, firstShape⟩ := pending_response_raw first before
  obtain ⟨right, lastPrelude, lastShape⟩ := pending_response_raw last after
  have same := returned_common_prefix_unique firstPrelude lastPrelude
    (List.IsPrefix.trans (⟨_, firstShape.symm⟩ : left <+: firstEngine.events) ordered)
    (⟨_, lastShape.symm⟩ : right <+: lastEngine.events)
  have firstLength := congrArg List.length firstShape
  have lastLength := congrArg List.length lastShape
  simp only [List.length_append, List.length_map, same.1] at firstLength lastLength
  omega

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {ticks : List (ActorTick runtime)} {pair : Pair} {Token : Type}

theorem actual_response_base_unique {initialWorld : World} {population : Population}
    (source : ActorJournal runtime (Population.empty initialWorld) ticks population)
    (first last : EngineWriteEntry ticks pair) (sameActor : first.actor = last.actor)
    (firstResponse : EngineResponse first) (lastResponse : EngineResponse last) :
    first.engine.events.length - firstResponse.source.writer.acknowledged.length =
      last.engine.events.length - lastResponse.source.writer.acknowledged.length := by
  have initialPresent : first.tick.before.actors last.actor = some first.engine := by
    simpa only [sameActor] using first.present
  rcases Nat.le_total first.position last.position with ordered | ordered
  · exact pending_response_base_unique firstResponse.pending lastResponse.pending firstResponse.source lastResponse.source
      (selected_events_prefix source ordered first.selected last.selected last.actor first.engine last.engine initialPresent last.present)
  · exact (pending_response_base_unique lastResponse.pending firstResponse.pending lastResponse.source firstResponse.source
      (selected_events_prefix source ordered last.selected first.selected last.actor last.engine first.engine last.present initialPresent)).symm

theorem registered_response_request_bytes
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {initialWorld : World} {population : Population}
    (source : ActorJournal runtime (Population.empty initialWorld) ticks population)
    (entry : EngineWriteEntry ticks pair) {position : Nat} {state : PhysicalState}
    (registered : Registered primitive position state) (current : WriteProgress)
    (stored : state.ledger entry.key = some current) : current.input.bytes = entry.request.left.data.toList := by
  obtain ⟨original, token, entered, key, input, before⟩ := registered_engine_source registered
    entry.actor entry.engine.events.length current stored
  have fields := CallKey.engine.inj key
  have sameRequest := actual_same_ordinal_request source original entry.selected entry.engine
    (by simpa only [fields.1] using entry.present) entry.running fields.2.symm entry.request entry.next entry.head
  simpa only [EngineWriteEntry.description, sameRequest] using (congrArg WriteDescription.bytes input).symm

-- §FS-host-boundary.caller: The final still-pending/error/lost write has its
-- exact response slice in the whole physical history. No final write return,
-- registration-cut witness or successful engine exit is required.
theorem actual_response_final_chunk
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    {initialWorld : World} {population : Population}
    (source : ActorJournal runtime (Population.empty initialWorld) ticks population)
    {final : PhysicalState} {records : List Record}
    (physical : SynchronizedJournal primitive 0 ticks .unborn records final)
    (entry : EngineWriteEntry ticks pair) (response : EngineResponse entry)
    (current : WriteProgress) (stored : final.ledger entry.key = some current) :
    response.source.writer.offset + current.committed ≤ response.source.context.bytes.size ∧
    records.flatMap (Record.bytesFor entry.key) =
      (response.source.context.bytes.extract response.source.writer.offset
        (response.source.writer.offset + current.committed)).data.toList := by
  obtain ⟨position, ordered, registered⟩ := physical.erase.registered (registered_unborn primitive)
  have input := registered_response_request_bytes source entry registered current stored
  have bound := current.bounded
  rw [input, Array.length_toList] at bound
  change current.committed ≤ entry.request.left.size at bound
  have payload := response.payload.2.1
  rw [payload, ByteArray.size_extract] at bound
  have sourceInside := response.source.writer.inside
  simp only [Nat.min_eq_left (Nat.min_le_left _ _)] at bound
  have extent : response.source.writer.offset + current.committed ≤
      min response.source.context.bytes.size (response.source.writer.offset + chunkMax) := by omega
  refine ⟨Nat.le_trans extent (Nat.min_le_left _ _), ?_⟩
  have nested : entry.request.left.extract 0 current.committed = response.source.context.bytes.extract
      response.source.writer.offset (response.source.writer.offset + current.committed) := by
    rw [payload, ByteArray.extract_extract, Nat.add_zero, Nat.min_eq_left extent]
  have bytes := actual_key_committed_prefix physical.erase entry.key current stored
  rw [input] at bytes
  have raw : records.flatMap (Record.bytesFor entry.key) = (entry.request.left.extract 0 current.committed).data.toList := by
    simpa only [ByteArray.data_extract, Array.toList_extract, List.extract, Nat.sub_zero, List.drop_zero] using bytes
  exact raw.trans (congrArg (fun value : ByteArray => value.data.toList) nested)

end LeanCage.Host.PrivateStreams
