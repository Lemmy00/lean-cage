import LeanCageHost.Entrypoint
import CallerProofs
import PacketProofs
import PublicationProofs.Writes

namespace LeanCage.Host.Entrypoint
open Filesystem

structure Response (events : List Program.Event) where
  packet : Filesystem.Result GatewayWire.Request
  response : Nat × GatewayWire.Value
  startup : List (Request × Reply)
  reading : List (Request × Reply)
  dispatching : List Program.Event
  writing : List (Request × Reply)
  ready : Returns Startup.descriptors startup (.ok ())
  read : Returns (Packet.read 0) reading packet
  command : Program.Returns (packetResponse packet) dispatching response
  bound : (GatewayWire.encodeResponse response.1 response.2).size ≤ GatewayWire.responseMax
  write : Returns (writeLoop ((GatewayWire.encodeResponse response.1 response.2).size + 1)
    1 (GatewayWire.encodeResponse response.1 response.2) 0) writing (.ok ())
  bytes : Publication.AcknowledgedWrites 1 (GatewayWire.encodeResponse response.1 response.2) 0 writing
  trace : events = startup.map Program.filesystemEvent ++ reading.map Program.filesystemEvent ++
    dispatching ++ writing.map Program.filesystemEvent

-- §FS-host-boundary.caller: Successful engine return requires actual complete bounded output.
theorem run_source {events : List Program.Event}
    (execution : Program.Returns Entrypoint.run events 0) : Nonempty (Response events) := by
  unfold Entrypoint.run at execution
  obtain ⟨startup, ready, afterStartup, readyRun, continuation, startupShape⟩ :=
    Program.returns_bind_split _ _ execution
  cases ready with
  | error error =>
    obtain ⟨_, same⟩ := Program.returns_pure _ continuation
    contradiction
  | ok readyValue =>
    cases readyValue
    obtain ⟨reading, packet, afterRead, readRun, afterPacket, readShape⟩ :=
      Program.returns_bind_split _ _ continuation
    obtain ⟨dispatching, response, afterDispatch, commandRun, afterResponse, dispatchShape⟩ :=
      Program.returns_bind_split _ _ afterPacket
    dsimp only at afterResponse
    split at afterResponse
    · obtain ⟨_, same⟩ := Program.returns_pure _ afterResponse
      contradiction
    · rename_i bounded
      obtain ⟨writing, result, ending, writeRun, final, writeShape⟩ :=
        Program.returns_bind_split _ _ afterResponse
      cases result with
      | error error =>
        obtain ⟨_, same⟩ := Program.returns_pure _ final
        contradiction
      | ok writtenValue =>
        cases writtenValue
        obtain ⟨rfl, _⟩ := Program.returns_pure _ final
        obtain ⟨startupSource, startupRun, startupEvents⟩ := Program.lift_filesystem_source _ readyRun
        obtain ⟨readSource, readRun, readEvents⟩ := Program.lift_filesystem_source _ readRun
        obtain ⟨writeSource, writeRun, writeEvents⟩ := Program.lift_filesystem_source _ writeRun
        refine ⟨⟨packet, response, startupSource, readSource, dispatching, writeSource,
          startupRun, readRun, commandRun, by omega, writeRun,
          Publication.writeLoop_source _ _ _ _ (Nat.zero_le _) writeRun, ?_⟩⟩
        simp only [startupShape, readShape, dispatchShape, writeShape, startupEvents, readEvents,
          writeEvents, List.append_nil, List.append_assoc]

theorem failure_status (failure : Filesystem.Failure) : (Commands.failureValue failure).1 ≠ 0 := by
  cases value : failure.errno <;> simp [Commands.failureValue, value]

-- §FS-host-boundary.caller: A success response cannot originate from a rejected input packet.
theorem response_success_packet {raw : Filesystem.Result GatewayWire.Request}
    {events : List Program.Event} {answer : GatewayWire.Value}
    (execution : Program.Returns (packetResponse raw) events (0, answer)) :
    ∃ request, raw = .ok request ∧ Program.Returns (Commands.run request) events (0, answer) := by
  cases raw with
  | error failure =>
    obtain ⟨_, same⟩ := Program.returns_pure _ execution
    have code := congrArg Prod.fst same
    exact False.elim (failure_status failure code.symm)
  | ok request => exact ⟨request, rfl, execution⟩

end LeanCage.Host.Entrypoint
