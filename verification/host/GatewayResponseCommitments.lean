import GatewayStreamExtents

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

variable {kernel : Contract} {runtime : PrimitiveActorRuntime kernel}
  {process : ProcessContract runtime} {child : ChildPrimitive kernel} {native : NativePrimitive kernel}
  {hostUid : Nat} {before after : Processes} {callers next : NativeProcesses}
  {ticks : List (ActorTick runtime)} {pair : Pair} {Token : Type}

-- §FS-host-boundary.caller: A still-pending actual response write contributes
-- exactly this source-selected encoded-response slice. It need never return.
theorem actual_pending_response_chunk
    {primitive : Primitive process child native hostUid before after callers next ticks pair Token}
    (entry : EngineWriteEntry ticks pair) (response : EngineResponse entry)
    (registeredAt : PhysicalState) {position : Nat} {records : List Record} {final : PhysicalState}
    (progress : ObservedJournal primitive position
      { registeredAt with ledger := registeredAt.ledger.set entry.key ⟨entry.description, 0, Nat.zero_le _, .pending⟩ }
      records final) :
    ∃ current, final.ledger entry.key = some current ∧ current.input = entry.description ∧
      response.source.writer.offset + current.committed ≤ response.source.context.bytes.size ∧
      records.flatMap (Record.bytesFor entry.key) =
        (response.source.context.bytes.extract response.source.writer.offset
          (response.source.writer.offset + current.committed)).data.toList := by
  have start : (registeredAt.ledger.set entry.key ⟨entry.description, 0, Nat.zero_le _, .pending⟩) entry.key =
      some ⟨entry.description, 0, Nat.zero_le _, .pending⟩ := by simp [Ledger.set]
  obtain ⟨current, stored, input, increased, bytes⟩ := progress.key_bytes entry.key _ start
  have bound := current.bounded
  rw [input] at bound
  change current.committed ≤ entry.request.left.data.toList.length at bound
  rw [Array.length_toList] at bound
  change current.committed ≤ entry.request.left.size at bound
  have payload := response.payload.2.1
  rw [payload, ByteArray.size_extract] at bound
  have sourceInside := response.source.writer.inside
  simp only [Nat.min_eq_left (Nat.min_le_left _ _)] at bound
  have extent : response.source.writer.offset + current.committed ≤
      min response.source.context.bytes.size (response.source.writer.offset + chunkMax) := by omega
  refine ⟨current, stored, input, Nat.le_trans extent (Nat.min_le_left _ _), ?_⟩
  have nested : entry.request.left.extract 0 current.committed =
      response.source.context.bytes.extract response.source.writer.offset
        (response.source.writer.offset + current.committed) := by
    rw [payload, ByteArray.extract_extract, Nat.add_zero, Nat.min_eq_left extent]
  have raw : records.flatMap (Record.bytesFor entry.key) =
      (entry.request.left.extract 0 current.committed).data.toList := by
    simpa only [segment, EngineWriteEntry.description, List.drop_zero, Nat.sub_zero,
      ByteArray.data_extract, Array.toList_extract, List.extract, Nat.sub_zero, List.drop_zero] using bytes
  exact raw.trans (congrArg (fun value : ByteArray => value.data.toList) nested)

-- §AR-host-boundary.interfaces.gateway: Earlier actual ACK prefixes and the
-- current pending extent join without a final writer ACK or engine return.
theorem response_prefix_with_pending (bytes : ByteArray) {offset extent : Nat}
    (_inside : offset + extent ≤ bytes.size) (acknowledged current : Bytes)
    (earlier : acknowledged = (bytes.extract 0 offset).data.toList)
    (pending : current = (bytes.extract offset (offset + extent)).data.toList) :
    acknowledged ++ current = (bytes.extract 0 (offset + extent)).data.toList := by
  rw [earlier, pending, ← ByteArray.toList_data_append, ByteArray.extract_append_extract,
    Nat.min_eq_left (by omega), Nat.max_eq_right (by omega)]

end LeanCage.Host.PrivateStreams
