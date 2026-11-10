import ReceiveProofs
import PublicationProofs

namespace LeanCage.Host.ExecutionProofs
open Filesystem
open ApplicationProofs

theorem lift_source {α : Type} (program : Program α)
    {events : List Program.Event} {value : α}
    (run : Run (ExceptT.lift program : Checked α) events value) :
    Program.Returns program events value := by
  change Program.Returns (program.bind (fun value => .pure (Except.ok value : Except Failure α)))
    events (Except.ok value : Except Failure α) at run
  obtain ⟨first, actual, last, source, final, shape⟩ := Program.returns_bind_split _ _ run
  obtain ⟨rfl, same⟩ := Program.returns_pure _ final
  cases same
  rw [shape]
  simpa only [List.append_nil] using source

-- §FS-host-boundary.acceptance: These are actual phases of executeRun, with one ordered trace.
structure Execution (request : GatewayWire.Request) (bundle : Validation.Bundle)
    (override : Option Nat) (events : List Program.Event) (answer : GatewayWire.Value) where
  policy : Policy.Accepted
  frozen : Snapshot.Frozen
  random : ByteArray
  duration : Nat
  transport : Transport.State
  directory : RunDirectory.Owned
  image : Filesystem.Result Unit
  input : Publication.Input
  output : Publication.Output
  preparing : List Program.Event
  randomizing : List (Request × Reply)
  timing : List Program.Event
  allocating : List (Request × Reply)
  imaging : List (Request × Reply)
  dispatching : List Program.Event
  cleaning : List Program.Event
  publishing : List (Request × Reply)
  prepare : Run (preparePolicy request bundle) preparing (policy, frozen)
  randomize : Returns (Directories.randomBytes 17 16 .empty) randomizing (.ok random)
  timeout : Run (requestDuration request policy override) timing duration
  initialized : Transport.State.init (Snapshot.hex random).toUTF8 bundle.identity.toUTF8
    policy.transport = .ok transport
  allocate : Returns RunDirectory.create allocating (.ok directory)
  archive : Returns (Image.create directory.directory.fd bundle
    (Image.entries (Snapshot.hex random) bundle.identity (request.command == GatewayWire.checkCommand)
      request.fault policy frozen)) imaging image
  dispatch : Program.Returns (dispatchImage (Snapshot.hex random) bundle
    (request.command == GatewayWire.checkCommand) policy directory duration transport image) dispatching input
  cleanup : Program.Returns (cleanupRun directory input) cleaning ()
  publish : Returns (Publication.publish request bundle input) publishing output
  projection : answer = output.outcome.wire output.metadata
  trace : events = preparing ++ randomizing.map Program.filesystemEvent ++ timing ++
    allocating.map Program.filesystemEvent ++ imaging.map Program.filesystemEvent ++
    dispatching ++ cleaning ++ publishing.map Program.filesystemEvent

-- §FS-host-boundary.acceptance: No phase receipt or VM result is assumed by the caller proof.
theorem execute_run_source (request : GatewayWire.Request) (bundle : Validation.Bundle)
    (override : Option Nat) {events : List Program.Event} {answer : GatewayWire.Value}
    (run : Run (executeRun request bundle override) events answer) :
    Nonempty (Execution request bundle override events answer) := by
  unfold executeRun at run
  obtain ⟨preparing, prepared, rest, prepare, run, prepareShape⟩ := bind_source _ _ run
  rcases prepared with ⟨policy, frozen⟩
  dsimp only at run
  obtain ⟨randomizing, random, rest, randomize, run, randomShape⟩ := bind_source _ _ run
  obtain ⟨timing, duration, rest, timeout, run, timeShape⟩ := bind_source _ _ run
  obtain ⟨initializing, transport, rest, initialized, run, initShape⟩ := bind_source _ _ run
  obtain ⟨initialization, rfl⟩ := checked_source _ initialized
  obtain ⟨allocating, directory, rest, allocate, run, allocateShape⟩ := bind_source _ _ run
  obtain ⟨imaging, image, rest, archive, run, imageShape⟩ := bind_source _ _ run
  obtain ⟨dispatching, input, rest, dispatch, run, dispatchShape⟩ := bind_source _ _ run
  obtain ⟨cleaning, cleaned, rest, cleanup, run, cleanupShape⟩ := bind_source _ _ run
  cases cleaned
  obtain ⟨publishing, output, rest, publish, run, publishShape⟩ := bind_source _ _ run
  obtain ⟨rfl, same⟩ := Program.returns_pure _ run
  have projection := Except.ok.inj same
  obtain ⟨randomSource, randomize, randomEvents⟩ := filesystem_source _ randomize
  obtain ⟨allocateSource, allocate, allocateEvents⟩ := filesystem_source _ allocate
  obtain ⟨imageSource, archive, imageEvents⟩ := Program.lift_filesystem_source _ (lift_source _ archive)
  obtain ⟨publishSource, publish, publishEvents⟩ := Program.lift_filesystem_source _ (lift_source _ publish)
  refine ⟨⟨policy, frozen, random, duration, transport, directory, image, input, output,
    preparing, randomSource, timing, allocateSource, imageSource, dispatching, cleaning, publishSource,
    prepare, randomize, timeout, initialization, allocate, archive, lift_source _ dispatch,
    lift_source _ cleanup, publish, projection, ?_⟩⟩
  simp only [prepareShape, randomShape, timeShape, initShape, allocateShape, imageShape,
    dispatchShape, cleanupShape, publishShape, randomEvents, allocateEvents, imageEvents,
    publishEvents, List.nil_append, List.append_nil, List.append_assoc]

end LeanCage.Host.ExecutionProofs
