import GatewayPublicationReadProfile
import FilesystemWriteSources

namespace LeanCage.Host.PrivateStreams
open Filesystem Kernel

-- §FS-host-boundary.caller: All copied-file branches retain positional reads;
-- the only application stream-read branch is the actual VM program slice.
theorem create_directory_positioned : RequestProgram PositionedReads RunDirectory.create :=
  Publishing.directory_profile_positioned RunDirectory.create_requests

theorem cleanup_directory_positioned (directory : RunDirectory.Owned) :
    RequestProgram PositionedReads (RunDirectory.cleanup directory) := by
  apply request_weaken (RunDirectory.cleanup_requests directory)
  intro request role reading
  simp only [RunDirectory.CleanupRequest, reading] at role

theorem release_directory_positioned (directory : RunDirectory.Owned) :
    RequestProgram PositionedReads (Validation.releaseDirectory directory) := by
  unfold Validation.releaseDirectory
  apply RequestProgram.call (by intro impossible; cases impossible)
  intro first
  dsimp only [Filesystem.Program.bind]
  apply RequestProgram.call (by intro impossible; cases impossible)
  intro second
  exact .pure _

private theorem runtime_no_filesystem {α : Type} {program : Program α}
    (profile : Program.RuntimeOnly program) {before : List Program.Event} {request : Request} {observed : Option Reply}
    (active : Program.Prefix program (before ++ [Program.filesystemPrefixEvent (request, observed)])) : False := by
  have selected := Program.runtime_only_prefix profile active (Program.filesystemPrefixEvent (request, observed)) (by simp)
  cases observed <;> exact selected

theorem validator_positioned (bundle : Validation.Bundle) (raw : ByteArray)
    {before : List Program.Event} {request : Request} {observed : Option Reply}
    (active : Program.Prefix (Validation.validateCopied bundle raw)
      (before ++ [Program.filesystemPrefixEvent (request, observed)])) : PositionedReads request := by
  obtain ⟨cut⟩ := ValidatorPrefixCuts.validate_copied_cut bundle raw active
  cases cut with
  | allocating source => exact selected_filesystem_profile create_directory_positioned source
  | writing allocated inside source trace => exact selected_filesystem_profile (write_new_positioned _ _ _ _) source
  | spawning written inside source trace =>
    exact False.elim (runtime_no_filesystem
      (.call (.spawn (Validation.validatorArguments bundle (written.allocated.directory.path ++ "/policy.json")))
        _ True.intro (fun _ => .pure _)) source)
  | observing spawned inside source trace =>
    exact False.elim (runtime_no_filesystem (observe_child_runtime_only _ _) source)
  | cleaningFailedWrite allocated prior error written inside source trace =>
    exact selected_filesystem_profile (cleanup_directory_positioned _) source
  | cleaningObserved observed inside reaped source trace =>
    exact selected_filesystem_profile (cleanup_directory_positioned _) source
  | releasingUnknown observed inside unknown source trace =>
    exact selected_filesystem_profile (release_directory_positioned _) source

theorem preparation_positioned (caller : GatewayWire.Request) (bundle : Validation.Bundle)
    {before : List Program.Event} {request : Request} {observed : Option Reply}
    (active : Program.Prefix (preparePolicy caller bundle).run
      (before ++ [Program.filesystemPrefixEvent (request, observed)])) : PositionedReads request := by
  obtain ⟨cut⟩ := PreparationPrefixCuts.prepare_policy_cut caller bundle active
  cases cut with
  | loading source => exact selected_filesystem_profile (load_policy_positioned _) source
  | validating context inside source trace => exact validator_positioned bundle context.raw source
  | copying context inside source trace => exact freeze_positioned _ _ _ source
  | revalidating context inside source trace => exact validator_positioned bundle context.policy.raw source

theorem image_entries_positioned (inode : Nat) (fd : UInt64) (entries : List Image.Entry) :
    RequestProgram PositionedReads (Image.writeEntries inode fd entries) := by
  induction entries generalizing inode with
  | nil => exact .pure _
  | cons entry rest ih =>
    unfold Image.writeEntries
    apply request_bind (write_loop_positioned _ _ _ _)
    intro written
    cases written with
    | error => exact .pure _
    | ok value =>
      apply request_bind (write_loop_positioned _ _ _ _)
      intro written
      cases written with
      | error => exact .pure _
      | ok value =>
        apply request_bind (write_loop_positioned _ _ _ _)
        intro written
        cases written with
        | error => exact .pure _
        | ok value => exact ih _

theorem image_content_positioned (fd : UInt64) (base : ByteArray) (overlay : List Image.Entry) :
    RequestProgram PositionedReads (Image.content fd base overlay) := by
  unfold Image.content
  apply request_bind (write_loop_positioned _ _ _ _)
  intro written
  cases written with
  | error => exact .pure _
  | ok value =>
    apply request_bind (write_loop_positioned _ _ _ _)
    intro written
    cases written with
    | error => exact .pure _
    | ok value => exact image_entries_positioned _ _ _

theorem image_positioned (fd : UInt64) (bundle : Validation.Bundle) (overlay : List Image.Entry) :
    RequestProgram PositionedReads (Image.create fd bundle overlay) := by
  unfold Image.create
  split
  · exact .pure _
  · apply request_bind (copy_identified_positioned _ _ _)
    intro copied
    cases copied with
    | error => exact .pure _
    | ok bytes =>
      apply RequestProgram.call (by intro impossible; cases impossible)
      intro opened
      dsimp only [Filesystem.Program.bind]
      split
      · exact .pure _
      · exact request_bind (image_content_positioned _ _ _) (close_positioned _)

theorem cleanup_run_positioned (directory : RunDirectory.Owned) (input : Publication.Input)
    {before : List Program.Event} {request : Request} {observed : Option Reply}
    (active : Program.Prefix (cleanupRun directory input)
      (before ++ [Program.filesystemPrefixEvent (request, observed)])) : PositionedReads request := by
  unfold cleanupRun at active
  split at active
  · rcases Program.last_bind_split _ _ active with first | ⟨first, value, inside, complete, last, trace⟩
    · exact selected_filesystem_profile (allowed := PositionedReads)
        (.call (by intro impossible; cases impossible) (fun _ => .pure _)) first
    · rcases Program.last_bind_split _ _ last with second | ⟨second, value, inside, complete, last, trace⟩
      · exact selected_filesystem_profile (allowed := PositionedReads)
          (.call (by intro impossible; cases impossible) (fun _ => .pure _)) second
      · exact False.elim (Program.pure_has_no_last _ _ _ last)
  · exact selected_filesystem_profile (cleanup_directory_positioned _) active

structure MachineRead (before : List Program.Event) (event : Program.Event) where
  bundle : Validation.Bundle
  directory : String
  duration : Nat
  transport : Transport.State
  source : WriteSources.Slice (α := VirtualMachine.Result)
    (VirtualMachine.run bundle directory duration transport) before event

def MachineRead.outer {inside before : List Program.Event} {event : Program.Event}
    (read : MachineRead inside event) (context : List Program.Event) (trace : before = context ++ inside) :
    MachineRead before event := { read with source := read.source.outer context trace }

theorem dispatch_stream_read {caller : GatewayWire.Request} {bundle : Validation.Bundle} {duration : Option Nat}
    (imaged : RunPrefixCuts.Imaged caller bundle duration)
    {before : List Program.Event} {request : Request} {observed : Option Reply}
    (active : Program.Prefix imaged.dispatchProgram (before ++ [Program.filesystemPrefixEvent (request, observed)]))
    (reading : request.op = .read) (stream : request.third = 0) :
    Nonempty (MachineRead before (Program.filesystemPrefixEvent (request, observed))) := by
  unfold RunPrefixCuts.Imaged.dispatchProgram dispatchImage at active
  cases actualImage : imaged.image with
  | error error =>
    simp only [actualImage] at active
    exact False.elim (Program.pure_has_no_last _ _ _ active)
  | ok value =>
    simp only [actualImage] at active
    rcases Program.last_bind_split _ _ active with machine | ⟨events, result, inside, ran, checked, trace⟩
    · exact ⟨⟨bundle, imaged.allocated.directory.path, imaged.allocated.setup.duration, imaged.allocated.setup.transport,
        ⟨[], before, machine, by simp⟩⟩⟩
    · have positioned := selected_filesystem_profile
        (hash_only_positioned (ReceiveProofs.receive_hashOnly _ _ _ _ _)) checked
      exact False.elim (positioned reading stream)

theorem run_stream_read (caller : GatewayWire.Request) (bundle : Validation.Bundle) (duration : Option Nat)
    {before : List Program.Event} {request : Request} {observed : Option Reply}
    (active : Program.Prefix (executeRun caller bundle duration).run
      (before ++ [Program.filesystemPrefixEvent (request, observed)]))
    (reading : request.op = .read) (stream : request.third = 0) :
    Nonempty (MachineRead before (Program.filesystemPrefixEvent (request, observed))) := by
  obtain ⟨cut⟩ := RunPrefixCuts.execute_run_cut caller bundle duration active
  cases cut with
  | preparing source => exact False.elim (preparation_positioned caller bundle source reading stream)
  | randomizing policy frozen preparing inside prepare source trace =>
    exact False.elim ((selected_filesystem_profile (Publishing.randomBytes_positioned _ _ _ (by decide)) source) reading stream)
  | allocating setup inside source trace => exact False.elim ((selected_filesystem_profile create_directory_positioned source) reading stream)
  | imaging allocated inside source trace => exact False.elim ((selected_filesystem_profile (image_positioned _ _ _) source) reading stream)
  | dispatching imaged inside source trace =>
    obtain ⟨read⟩ := dispatch_stream_read imaged source reading stream
    exact ⟨read.outer imaged.events trace⟩
  | cleaning dispatched inside source trace => exact False.elim (cleanup_run_positioned _ _ source reading stream)
  | publishing cleaned inside source trace =>
    exact False.elim ((selected_filesystem_profile (Publishing.publish_positioned _ _ _) source) reading stream)

theorem caller_stream_read (caller : GatewayWire.Request) (duration : Option Nat)
    {before : List Program.Event} {request : Request} {observed : Option Reply}
    (active : Program.Prefix (execute caller duration)
      (before ++ [Program.filesystemPrefixEvent (request, observed)]))
    (reading : request.op = .read) (stream : request.third = 0) :
    Nonempty (MachineRead before (Program.filesystemPrefixEvent (request, observed))) := by
  obtain ⟨cut⟩ := CallerPrefixCuts.execute_checked_cut caller duration active
  cases cut with
  | selecting source => exact False.elim ((selected_filesystem_profile (load_bundle_positioned _) source) reading stream)
  | checking context inside source trace => exact False.elim ((selected_filesystem_profile (check_bundle_positioned _) source) reading stream)
  | identifying context inside source trace => exact False.elim ((selected_filesystem_profile (engine_identity_positioned _) source) reading stream)
  | authenticating context inside source trace =>
    have positioned : RequestProgram PositionedReads (CallerPrefixCuts.keyGate context.checked.selected.bundle) :=
      request_bind (key_positioned _) (fun _ => .pure _)
    exact False.elim ((selected_filesystem_profile positioned source) reading stream)
  | loadingPolicy context inside source trace => exact False.elim ((selected_filesystem_profile (load_policy_positioned _) source) reading stream)
  | validating context raw loading loaded inside source trace => exact False.elim (validator_positioned context.bundle raw source reading stream)
  | executing context inside command source trace =>
    obtain ⟨read⟩ := run_stream_read caller context.bundle duration source reading stream
    exact ⟨read.outer context.events trace⟩
  | retrieving context inside command source trace =>
    exact False.elim ((selected_filesystem_profile (report_positioned _ _) source) reading stream)

end LeanCage.Host.PrivateStreams
