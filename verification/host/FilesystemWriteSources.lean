import FilesystemWriteSources.ReadOnly
import ReceiveProofs

namespace LeanCage.Host.Kernel.WriteSources
open Filesystem
set_option maxHeartbeats 4000000

structure Slice {α : Type} (program : Program α) (before : List Program.Event) (event : Program.Event) where
  context : List Program.Event
  inside : List Program.Event
  active : Program.Prefix program (inside ++ [event])
  trace : before = context ++ inside

def Slice.outer {α : Type} {program : Program α} {inside before : List Program.Event} {event : Program.Event}
    (source : Slice program inside event) (context : List Program.Event) (trace : before = context ++ inside) :
    Slice program before event :=
  ⟨context ++ source.context, source.inside, source.active,
    trace.trans ((congrArg (context ++ ·) source.trace).trans
      (List.append_assoc context source.context source.inside).symm)⟩

-- §FS-host-boundary.caller: These are actual source phases, with cumulative producers.
-- File allocation/IPC identity are derived by their physical consumers, not these role names.
inductive Call (before : List Program.Event) (event : Program.Event) : Type 1 where
  | validator (bundle : Validation.Bundle) (raw : ByteArray) (allocated : ValidatorPrefixCuts.Allocated)
      (source : Slice (α := Filesystem.Result Unit) (Program.liftFilesystem (allocated.writeProgram raw)) before event)
  | image {request : GatewayWire.Request} {bundle : Validation.Bundle} {duration : Option Nat}
      (allocated : RunPrefixCuts.Allocated request bundle duration)
      (source : Slice (α := Filesystem.Result Unit) (Program.liftFilesystem allocated.imageProgram) before event)
  | machine {request : GatewayWire.Request} {bundle : Validation.Bundle} {duration : Option Nat}
      (imaged : RunPrefixCuts.Imaged request bundle duration)
      (source : Slice (α := Publication.Input) imaged.dispatchProgram before event)
  | publication {request : GatewayWire.Request} {bundle : Validation.Bundle} {duration : Option Nat}
      (cleaned : RunPrefixCuts.Cleaned request bundle duration)
      (source : Slice (α := Publication.Output)
        (Program.liftFilesystem (Publication.publish request bundle cleaned.dispatched.input)) before event)

def Call.outer {inside before : List Program.Event} {event : Program.Event}
    (source : Call inside event) (context : List Program.Event) (trace : before = context ++ inside) :
    Call before event := by
  cases source with
  | validator bundle raw allocated source => exact .validator bundle raw allocated (source.outer context trace)
  | image allocated source => exact .image allocated (source.outer context trace)
  | machine imaged source => exact .machine imaged (source.outer context trace)
  | publication cleaned source => exact .publication cleaned (source.outer context trace)

private theorem runtime_no_filesystem {α : Type} {program : Program α}
    (profile : Program.RuntimeOnly program) {before : List Program.Event} {request : Request}
    {observed : Option Reply}
    (active : Program.Prefix program (before ++ [Program.filesystemPrefixEvent (request, observed)])) : False := by
  have selected := Program.runtime_only_prefix profile active (Program.filesystemPrefixEvent (request, observed)) (by simp)
  cases observed <;> exact selected

-- §FS-host-boundary.ownership: A validator write occurs only in its actual fresh policy writer.
theorem validator_call (bundle : Validation.Bundle) (raw : ByteArray)
    {before : List Program.Event} {request : Request} {observed : Option Reply}
    (active : Program.Prefix (Validation.validateCopied bundle raw)
      (before ++ [Program.filesystemPrefixEvent (request, observed)])) (writing : request.op = .write) :
    Nonempty (Call before (Program.filesystemPrefixEvent (request, observed))) := by
  obtain ⟨cut⟩ := ValidatorPrefixCuts.validate_copied_cut bundle raw active
  cases cut with
  | allocating active => exact False.elim (selected_filesystem_profile create_directory_no_write active writing)
  | writing allocated inside active trace => exact ⟨.validator bundle raw allocated ⟨allocated.events, inside, active, trace⟩⟩
  | spawning written inside active trace =>
    have onlyRuntime : Program.RuntimeOnly (written.allocated.spawnProgram bundle) :=
      .call (.spawn (Validation.validatorArguments bundle (written.allocated.directory.path ++ "/policy.json")))
        _ True.intro (fun _ => .pure _)
    exact False.elim (runtime_no_filesystem onlyRuntime active)
  | observing spawned inside active trace =>
    exact False.elim (runtime_no_filesystem (observe_child_runtime_only _ _) active)
  | cleaningFailedWrite allocated prior error written inside active trace =>
    exact False.elim (selected_filesystem_profile (cleanup_directory_no_write _) active writing)
  | cleaningObserved observed inside reaped active trace =>
    exact False.elim (selected_filesystem_profile (cleanup_directory_no_write _) active writing)
  | releasingUnknown observed inside unknown active trace =>
    exact False.elim (selected_filesystem_profile (validator_release_no_write _) active writing)

theorem prepare_call (caller : GatewayWire.Request) (bundle : Validation.Bundle)
    {before : List Program.Event} {request : Request} {observed : Option Reply}
    (active : Program.Prefix (preparePolicy caller bundle).run
      (before ++ [Program.filesystemPrefixEvent (request, observed)])) (writing : request.op = .write) :
    Nonempty (Call before (Program.filesystemPrefixEvent (request, observed))) := by
  obtain ⟨cut⟩ := PreparationPrefixCuts.prepare_policy_cut caller bundle active
  cases cut with
  | loading active => exact False.elim (selected_filesystem_profile (load_policy_no_write _) active writing)
  | validating context inside active trace =>
    obtain ⟨source⟩ := validator_call bundle context.raw active writing
    exact ⟨source.outer context.events trace⟩
  | copying context inside active trace =>
    exact False.elim (selected_filesystem_profile (input_no_write (Snapshot.freeze_input _ _ _)) active writing)
  | revalidating context inside active trace =>
    obtain ⟨source⟩ := validator_call bundle context.policy.raw active writing
    exact ⟨source.outer context.events trace⟩

private theorem cleanup_no_write (directory : RunDirectory.Owned) (input : Publication.Input)
    {before : List Program.Event} {request : Request} {observed : Option Reply}
    (active : Program.Prefix (cleanupRun directory input)
      (before ++ [Program.filesystemPrefixEvent (request, observed)])) (writing : request.op = .write) : False := by
  unfold cleanupRun at active
  split at active
  · rcases Program.last_bind_split _ _ active with first | ⟨first, value, inside, complete, last, trace⟩
    · exact selected_filesystem_profile (allowed := NoWrite)
        (.call (by intro wrong; cases wrong) (fun _ => .pure _)) first writing
    · rcases Program.last_bind_split _ _ last with second | ⟨second, value, inside, complete, last, trace⟩
      · exact selected_filesystem_profile (allowed := NoWrite)
          (.call (by intro wrong; cases wrong) (fun _ => .pure _)) second writing
      · exact Program.pure_has_no_last _ _ _ last
  · exact selected_filesystem_profile (cleanup_directory_no_write _) active writing

-- §FS-host-boundary.caller: The same run prefix retains real policy/allocation/image/VM data.
theorem run_call (caller : GatewayWire.Request) (bundle : Validation.Bundle) (duration : Option Nat)
    {before : List Program.Event} {request : Request} {observed : Option Reply}
    (active : Program.Prefix (executeRun caller bundle duration).run
      (before ++ [Program.filesystemPrefixEvent (request, observed)])) (writing : request.op = .write) :
    Nonempty (Call before (Program.filesystemPrefixEvent (request, observed))) := by
  obtain ⟨cut⟩ := RunPrefixCuts.execute_run_cut caller bundle duration active
  cases cut with
  | preparing active => exact prepare_call caller bundle active writing
  | randomizing policy frozen preparing inside prepare active trace =>
    exact False.elim (selected_filesystem_profile random_no_write active writing)
  | allocating setup inside active trace =>
    exact False.elim (selected_filesystem_profile create_directory_no_write active writing)
  | imaging allocated inside active trace => exact ⟨.image allocated ⟨allocated.events, inside, active, trace⟩⟩
  | dispatching imaged inside active trace => exact ⟨.machine imaged ⟨imaged.events, inside, active, trace⟩⟩
  | cleaning dispatched inside active trace => exact False.elim (cleanup_no_write _ _ active writing)
  | publishing cleaned inside active trace => exact ⟨.publication cleaned ⟨cleaned.events, inside, active, trace⟩⟩

theorem caller_call (caller : GatewayWire.Request) (duration : Option Nat)
    {before : List Program.Event} {request : Request} {observed : Option Reply}
    (active : Program.Prefix (execute caller duration)
      (before ++ [Program.filesystemPrefixEvent (request, observed)])) (writing : request.op = .write) :
    Nonempty (Call before (Program.filesystemPrefixEvent (request, observed))) := by
  obtain ⟨cut⟩ := CallerPrefixCuts.execute_checked_cut caller duration active
  cases cut with
  | selecting active => exact False.elim (selected_filesystem_profile (load_bundle_no_write _) active writing)
  | checking context inside active trace =>
    exact False.elim (selected_filesystem_profile (check_bundle_no_write _) active writing)
  | identifying context inside active trace =>
    exact False.elim (selected_filesystem_profile (engine_identity_no_write _) active writing)
  | authenticating context inside active trace =>
    exact False.elim (selected_filesystem_profile (key_gate_no_write _) active writing)
  | loadingPolicy context inside active trace =>
    exact False.elim (selected_filesystem_profile (load_policy_no_write _) active writing)
  | validating context raw loading load inside active trace =>
    obtain ⟨source⟩ := validator_call context.bundle raw active writing
    exact ⟨source.outer (context.events ++ loading.map Program.filesystemEvent) (by
      simpa only [List.append_assoc] using trace)⟩
  | executing context inside command active trace =>
    obtain ⟨source⟩ := run_call caller context.bundle duration active writing
    exact ⟨source.outer context.events trace⟩
  | retrieving context inside command active trace =>
    exact False.elim (selected_filesystem_profile (read_only_no_write (Retrieval.report_readOnly _ _)) active writing)

-- §FS-host-boundary.acceptance: Arbitrary CLI/native paths, loss and setup failure remain.
theorem command_call (caller : GatewayWire.Request)
    {before : List Program.Event} {request : Request} {observed : Option Reply}
    (active : Program.Prefix (Commands.run caller)
      (before ++ [Program.filesystemPrefixEvent (request, observed)])) (writing : request.op = .write) :
    Nonempty (Call before (Program.filesystemPrefixEvent (request, observed))) := by
  obtain ⟨effective, duration, invocation, source⟩ := Commands.run_prefix_source caller active
  exact caller_call effective duration source writing

end LeanCage.Host.Kernel.WriteSources
