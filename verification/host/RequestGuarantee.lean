import ExecutionProofs
import PublicationConnection
import VirtualMachineProofs.Run
import RunDirectoryProofs.Source
import ImageProofs.Source

namespace LeanCage.Host.RequestGuarantee
open Filesystem
open ApplicationProofs

def statusField (value : GatewayWire.Value) : Option String :=
  match value with
  | .object fields => match ((fields.find? (fun field => field.1 == "status")).map
      (fun field => field.2) : Option GatewayWire.Value) with
    | some (.string status) => some status
    | _ => none
  | _ => none

theorem wire_status (outcome : Outcome) (metadata : GatewayWire.Value) :
    statusField (outcome.wire metadata) = some outcome.status := rfl

-- §FS-host-boundary.acceptance: The actual VM producer precedes the same receive operation.
theorem dispatch_complete_source (request : String) (bundle : Validation.Bundle) (preflight : Bool)
    (policy : Policy.Accepted) (directory : RunDirectory.Owned) (duration : Nat)
    (transport : Transport.State) (image : Filesystem.Result Unit)
    {events : List Program.Event} {input : Publication.Input}
    (run : Program.Returns (dispatchImage request bundle preflight policy directory duration transport image)
      events input) (complete : input.outcome.status = "complete") :
    image = .ok () ∧ ∃ vm invoking receiving,
      Program.Returns (VirtualMachine.run bundle directory.path duration transport) invoking vm ∧
      Returns (receive request bundle preflight policy vm) receiving input ∧
      events = invoking ++ receiving.map Program.filesystemEvent := by
  cases image with
  | error error =>
    obtain ⟨_, same⟩ := Program.returns_pure _ run
    cases same
    simp [incomplete] at complete
  | ok value =>
    cases value
    obtain ⟨invoking, vm, last, invoked, received, trace⟩ := Program.returns_bind_split _ _ run
    obtain ⟨receiving, copied, shape⟩ := Program.lift_filesystem_source _ received
    exact ⟨rfl, vm, invoking, receiving, invoked, copied, by rw [trace, shape]⟩

structure CompleteRun (request : GatewayWire.Request) (bundle : Validation.Bundle)
    (override : Option Nat) (events : List Program.Event) (answer : GatewayWire.Value) where
  source : ExecutionProofs.Execution request bundle override events answer
  vm : VirtualMachine.Result
  invoking : List Program.Event
  receiving : List (Request × Reply)
  connection : Option UInt64
  stream : List Transport.Event
  image : source.image = .ok ()
  vmRun : Program.Returns (VirtualMachine.run bundle source.directory.path source.duration source.transport) invoking vm
  receiveRun : Returns (receive (Snapshot.hex source.random) bundle
    (request.command == GatewayWire.checkCommand) source.policy vm) receiving source.input
  reception : ReceiveProofs.Complete (Snapshot.hex source.random) bundle
    (request.command == GatewayWire.checkCommand) source.policy vm receiving source.input
  runDirectory : RunDirectory.Creation source.allocating source.directory
  archive : Image.Creation source.directory.directory.fd bundle
    (Image.entries (Snapshot.hex source.random) bundle.identity (request.command == GatewayWire.checkCommand)
      request.fault source.policy source.frozen) source.imaging
  vmBytes : vm.transport = source.transport.run stream
  reads : VirtualMachine.ReadSubsequence connection invoking stream
  framing : Transport.eventsWire stream =
    (Transport.identityPrefix (Snapshot.hex source.random).toUTF8 bundle.identity.toUTF8).data.toList ++
      Transport.frameWire reception.transport.frames
  eof : Transport.Event.eof ∈ stream
  outputComplete : source.output.outcome.status = "complete"
  captures : source.output.outcome.stdout = source.input.outcome.stdout ∧
    source.output.outcome.stderr = source.input.outcome.stderr
  files : source.output.outcome.files = source.input.outcome.files
  report : source.output.outcome.report =
    vm.transport.report?.bind (Artifacts.knownReport (request.command == GatewayWire.checkCommand))
  stdoutBound : source.output.outcome.stdout.size ≤ source.policy.transport.stdoutMax
  stderrBound : source.output.outcome.stderr.size ≤ source.policy.transport.stderrMax
  workspaceBound : Artifacts.fileBytes source.output.outcome.files ≤ source.policy.transport.workspaceMax
  inodeBound : source.output.outcome.files.length ≤ source.policy.transport.inodesMax

-- §FS-host-boundary.acceptance: Complete wire output has a same-call, bounded artifact producer.
theorem execute_complete (request : GatewayWire.Request) (bundle : Validation.Bundle)
    (override : Option Nat) {events : List Program.Event} {answer : GatewayWire.Value}
    (run : Run (executeRun request bundle override) events answer)
    (complete : statusField answer = some "complete") :
    Nonempty (CompleteRun request bundle override events answer) := by
  obtain ⟨source⟩ := ExecutionProofs.execute_run_source request bundle override run
  rw [source.projection, wire_status] at complete
  have outputComplete : source.output.outcome.status = "complete" := Option.some.inj complete
  have unchanged := Publication.publish_complete_preserved request bundle source.input source.publish outputComplete
  obtain ⟨imageReady, vm, invoking, receiving, vmRun, receiveRun, _⟩ :=
    dispatch_complete_source (Snapshot.hex source.random) bundle
      (request.command == GatewayWire.checkCommand) source.policy source.directory source.duration
      source.transport source.image source.dispatch unchanged.1
  obtain ⟨reception⟩ := ReceiveProofs.receive_complete _ _ _ _ _ receiveRun unchanged.1
  obtain ⟨connection, ⟨stream, vmBytes, reads⟩, _⟩ := VirtualMachine.run_source _ _ _ _ vmRun
  have finished : (source.transport.run stream).finish = .ok reception.transport := by
    rw [← vmBytes]
    exact reception.finish
  have framing := Transport.accepted_stream _ _ _ _ source.initialized stream _ finished
  have eof := Transport.accepted_has_eof _ _ _ _ source.initialized stream _ finished
  have bounds := ReceiveProofs.receive_bounds _ _ _ _ _ receiveRun unchanged.1
  have report := (Publication.publish_report _ _ _ source.publish).trans
    (ReceiveProofs.receive_report _ _ _ _ _ receiveRun)
  have archiveRun := source.archive
  rw [imageReady] at archiveRun
  refine ⟨⟨source, vm, invoking, receiving, connection, stream, imageReady, vmRun, receiveRun,
    reception, RunDirectory.create_source source.allocate, Image.create_source _ _ _ archiveRun,
    vmBytes, reads, framing.1, eof, outputComplete, ⟨unchanged.2.1, unchanged.2.2.1⟩,
    unchanged.2.2.2, report, ?_, ?_, ?_, ?_⟩⟩
  all_goals simpa only [unchanged.2.1, unchanged.2.2.1, unchanged.2.2.2] using
    (by first | exact bounds.1 | exact bounds.2.1 | exact bounds.2.2.1 | exact bounds.2.2.2)

end LeanCage.Host.RequestGuarantee
