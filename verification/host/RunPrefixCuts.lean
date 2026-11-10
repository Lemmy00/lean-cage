import ExecutionProofs
import PrefixOrigins

namespace LeanCage.Host.RunPrefixCuts
open Filesystem ApplicationProofs

structure Setup (request : GatewayWire.Request) (bundle : Validation.Bundle) (override : Option Nat) where
  policy : Policy.Accepted
  frozen : Snapshot.Frozen
  random : ByteArray
  duration : Nat
  transport : Transport.State
  preparing : List Program.Event
  randomizing : List (Request × Reply)
  timing : List Program.Event
  prepare : Run (preparePolicy request bundle) preparing (policy, frozen)
  randomize : Returns (Directories.randomBytes 17 16 .empty) randomizing (.ok random)
  durationRun : Run (requestDuration request policy override) timing duration
  initialization : Transport.State.init (Snapshot.hex random).toUTF8 bundle.identity.toUTF8
    policy.transport = .ok transport

def Setup.events {request bundle override} (setup : Setup request bundle override) : List Program.Event :=
  setup.preparing ++ setup.randomizing.map Program.filesystemEvent ++ setup.timing

structure Allocated (request : GatewayWire.Request) (bundle : Validation.Bundle) (override : Option Nat) where
  setup : Setup request bundle override
  directory : RunDirectory.Owned
  allocating : List (Request × Reply)
  allocate : Returns RunDirectory.create allocating (.ok directory)

def Allocated.events {request bundle override} (context : Allocated request bundle override) : List Program.Event :=
  context.setup.events ++ context.allocating.map Program.filesystemEvent

def Allocated.imageProgram {request bundle override} (context : Allocated request bundle override) :=
  Image.create context.directory.directory.fd bundle
    (Image.entries (Snapshot.hex context.setup.random) bundle.identity
      (request.command == GatewayWire.checkCommand) request.fault context.setup.policy context.setup.frozen)

structure Imaged (request : GatewayWire.Request) (bundle : Validation.Bundle) (override : Option Nat) where
  allocated : Allocated request bundle override
  image : Filesystem.Result Unit
  imaging : List (Request × Reply)
  archive : Returns allocated.imageProgram imaging image

def Imaged.events {request bundle override} (context : Imaged request bundle override) : List Program.Event :=
  context.allocated.events ++ context.imaging.map Program.filesystemEvent

def Imaged.dispatchProgram {request bundle override} (context : Imaged request bundle override) :=
  dispatchImage (Snapshot.hex context.allocated.setup.random) bundle
    (request.command == GatewayWire.checkCommand) context.allocated.setup.policy context.allocated.directory
    context.allocated.setup.duration context.allocated.setup.transport context.image

structure Dispatched (request : GatewayWire.Request) (bundle : Validation.Bundle) (override : Option Nat) where
  imaged : Imaged request bundle override
  input : Publication.Input
  dispatching : List Program.Event
  dispatch : Program.Returns imaged.dispatchProgram dispatching input

def Dispatched.events {request bundle override} (context : Dispatched request bundle override) : List Program.Event :=
  context.imaged.events ++ context.dispatching

structure Cleaned (request : GatewayWire.Request) (bundle : Validation.Bundle) (override : Option Nat) where
  dispatched : Dispatched request bundle override
  cleaning : List Program.Event
  cleanup : Program.Returns (cleanupRun dispatched.imaged.allocated.directory dispatched.input) cleaning ()

def Cleaned.events {request bundle override} (context : Cleaned request bundle override) : List Program.Event :=
  context.dispatched.events ++ context.cleaning

-- §FS-host-boundary.ownership: Every phase carries actual earlier producers and its exact trace.
inductive Cut (request : GatewayWire.Request) (bundle : Validation.Bundle) (override : Option Nat)
    (before : List Program.Event) (event : Program.Event) : Type 1 where
  | preparing (active : Program.Prefix (preparePolicy request bundle).run (before ++ [event]))
  | randomizing (policy : Policy.Accepted) (frozen : Snapshot.Frozen)
      (preparing inside : List Program.Event)
      (prepare : Run (preparePolicy request bundle) preparing (policy, frozen))
      (active : Program.Prefix (Program.liftFilesystem (Directories.randomBytes 17 16 .empty)) (inside ++ [event]))
      (trace : before = preparing ++ inside)
  | allocating (context : Setup request bundle override) (inside : List Program.Event)
      (active : Program.Prefix (Program.liftFilesystem RunDirectory.create) (inside ++ [event]))
      (trace : before = context.events ++ inside)
  | imaging (context : Allocated request bundle override) (inside : List Program.Event)
      (active : Program.Prefix (Program.liftFilesystem context.imageProgram) (inside ++ [event]))
      (trace : before = context.events ++ inside)
  | dispatching (context : Imaged request bundle override) (inside : List Program.Event)
      (active : Program.Prefix context.dispatchProgram (inside ++ [event]))
      (trace : before = context.events ++ inside)
  | cleaning (context : Dispatched request bundle override) (inside : List Program.Event)
      (active : Program.Prefix (cleanupRun context.imaged.allocated.directory context.input) (inside ++ [event]))
      (trace : before = context.events ++ inside)
  | publishing (context : Cleaned request bundle override) (inside : List Program.Event)
      (active : Program.Prefix (Program.liftFilesystem
        (Publication.publish request bundle context.dispatched.input)) (inside ++ [event]))
      (trace : before = context.events ++ inside)

-- §FS-host-boundary.acceptance: A lost/interrupted call retains its actual active run phase.
theorem execute_run_cut (request : GatewayWire.Request) (bundle : Validation.Bundle) (override : Option Nat)
    {before : List Program.Event} {event : Program.Event}
    (active : Program.Prefix (executeRun request bundle override).run (before ++ [event])) :
    Nonempty (Cut request bundle override before event) := by
  unfold executeRun at active
  rcases last_checked_bind _ _ active with preparing | ⟨preparing, prepared, afterPrepare, prepare, rest, prepareShape⟩
  · exact ⟨.preparing preparing⟩
  · rcases prepared with ⟨policy, frozen⟩
    dsimp only at rest
    rcases last_checked_bind _ _ rest with randomizing |
        ⟨randomizing, random, afterRandom, randomize, rest, randomShape⟩
    · exact ⟨.randomizing policy frozen preparing afterPrepare prepare randomizing prepareShape⟩
    · rcases last_checked_bind _ _ rest with timing |
          ⟨timing, duration, afterTime, timeout, rest, timeShape⟩
      · exact False.elim (duration_has_no_last request policy override _ _ timing)
      · rcases last_checked_bind _ _ rest with initializing |
            ⟨initializing, transport, afterInit, initialized, rest, initShape⟩
        · exact False.elim (checked_has_no_last _ _ _ initializing)
        · obtain ⟨initialization, initEmpty⟩ := checked_source _ initialized
          obtain ⟨randomSource, randomRun, randomEvents⟩ := filesystem_source _ randomize
          let setup : Setup request bundle override :=
            ⟨policy, frozen, random, duration, transport, preparing, randomSource, timing,
              prepare, randomRun, timeout, initialization⟩
          have setupShape : before = setup.events ++ afterInit := by
            simp only [Setup.events, setup, prepareShape, randomShape, timeShape, initShape,
              randomEvents, initEmpty, List.nil_append, List.append_assoc]
          rcases last_checked_bind _ _ rest with allocating |
              ⟨allocating, directory, afterAllocate, allocate, rest, allocateShape⟩
          · exact ⟨.allocating setup afterInit allocating setupShape⟩
          · obtain ⟨allocateSource, allocateRun, allocateEvents⟩ := filesystem_source _ allocate
            let allocated : Allocated request bundle override := ⟨setup, directory, allocateSource, allocateRun⟩
            have allocatedShape : before = allocated.events ++ afterAllocate := by
              simp only [Allocated.events, allocated, setupShape, allocateShape, allocateEvents, List.append_assoc]
            rcases last_checked_bind _ _ rest with imaging |
                ⟨imaging, image, afterImage, archive, rest, imageShape⟩
            · exact ⟨.imaging allocated afterAllocate (lifted_prefix_source _ imaging) allocatedShape⟩
            · obtain ⟨imageSource, archiveRun, imageEvents⟩ :=
                Program.lift_filesystem_source _ (ExecutionProofs.lift_source _ archive)
              let imaged : Imaged request bundle override := ⟨allocated, image, imageSource, archiveRun⟩
              have imagedShape : before = imaged.events ++ afterImage := by
                simp only [Imaged.events, imaged, allocatedShape, imageShape, imageEvents, List.append_assoc]
              rcases last_checked_bind _ _ rest with dispatching |
                  ⟨dispatching, input, afterDispatch, dispatch, rest, dispatchShape⟩
              · exact ⟨.dispatching imaged afterImage (lifted_prefix_source _ dispatching) imagedShape⟩
              · let dispatched : Dispatched request bundle override :=
                  ⟨imaged, input, dispatching, ExecutionProofs.lift_source _ dispatch⟩
                have dispatchedShape : before = dispatched.events ++ afterDispatch := by
                  simp only [Dispatched.events, dispatched, imagedShape, dispatchShape, List.append_assoc]
                rcases last_checked_bind _ _ rest with cleaning |
                    ⟨cleaning, cleaned, afterCleanup, cleanup, rest, cleanupShape⟩
                · exact ⟨.cleaning dispatched afterDispatch (lifted_prefix_source _ cleaning) dispatchedShape⟩
                · cases cleaned
                  let context : Cleaned request bundle override :=
                    ⟨dispatched, cleaning, ExecutionProofs.lift_source _ cleanup⟩
                  have cleanedShape : before = context.events ++ afterCleanup := by
                    simp only [Cleaned.events, context, dispatchedShape, cleanupShape, List.append_assoc]
                  rcases last_checked_bind _ _ rest with publishing |
                      ⟨publishing, output, inside, published, last, publishShape⟩
                  · exact ⟨.publishing context afterCleanup (lifted_prefix_source _ publishing) cleanedShape⟩
                  · exact False.elim (Program.pure_has_no_last _ _ _ last)

end LeanCage.Host.RunPrefixCuts
