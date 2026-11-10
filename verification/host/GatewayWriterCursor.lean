import GatewayResponseCommitments

namespace LeanCage.Host.PrivateStreams
open Kernel Filesystem

private theorem response_ack_event_injective (first last : Request × Reply)
    (same : Program.filesystemEvent first = Program.filesystemEvent last) : first = last := by
  rcases first with ⟨first, firstReply⟩
  rcases last with ⟨last, lastReply⟩
  cases same
  rfl

-- §FS-host-boundary.caller: One actual ACK advances the next writer cursor
-- by precisely its observed count. The actual raw prefixes, not equal payloads
-- or a monotone bound, determine this equality.
theorem pending_response_one_ack {firstEngine lastEngine : EngineState} {firstRequest lastRequest : Request}
    (first : EntrypointWriterPrefix.PendingCut firstEngine firstRequest)
    (last : EntrypointWriterPrefix.PendingCut lastEngine lastRequest)
    (firstResponse : EntrypointWriterPrefix.ResponseFrontier first.occurrence.logicalBefore firstRequest none)
    (lastResponse : EntrypointWriterPrefix.ResponseFrontier last.occurrence.logicalBefore lastRequest none)
    (reply : Reply)
    (events : lastEngine.events = firstEngine.events ++ [Program.filesystemEvent (firstRequest, reply)]) :
    lastResponse.writer.acknowledged = firstResponse.writer.acknowledged ++ [(firstRequest, reply)] ∧
      lastResponse.writer.offset = firstResponse.writer.offset + reply.1.toNat := by
  obtain ⟨left, before, firstShape⟩ := pending_response_raw first firstResponse
  obtain ⟨right, after, lastShape⟩ := pending_response_raw last lastResponse
  have ordered : firstEngine.events <+: lastEngine.events := ⟨_, events.symm⟩
  have same := returned_common_prefix_unique before after
    (List.IsPrefix.trans (⟨_, firstShape.symm⟩ : left <+: firstEngine.events) ordered)
    (⟨_, lastShape.symm⟩ : right <+: lastEngine.events)
  have mapped : lastResponse.writer.acknowledged.map Program.filesystemEvent =
      (firstResponse.writer.acknowledged ++ [(firstRequest, reply)]).map Program.filesystemEvent := by
    apply List.append_cancel_left (as := left)
    simpa only [firstShape, lastShape, ← same.1, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc] using events
  have exactCalls := (List.map_inj_right response_ack_event_injective).mp mapped
  refine ⟨exactCalls, ?_⟩
  have initial := acknowledged_extent firstResponse.writer.progress
  have final := acknowledged_extent lastResponse.writer.progress
  rw [exactCalls] at final
  simpa only [acknowledgedExtent, List.map_append, List.sum_append, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Nat.zero_add, initial] using final

end LeanCage.Host.PrivateStreams
