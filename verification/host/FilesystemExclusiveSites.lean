import FilesystemRunFiles

namespace LeanCage.Host.Kernel
open Filesystem

private theorem create_not_exclusive : RequestProgram (fun request => ¬ ExclusiveFile request) RunDirectory.create := by
  apply request_weaken RunDirectory.create_requests
  intro request source exclusive
  simp only [RunDirectory.DirectoryRequest, exclusive.1, exclusive.2] at source
  exact (by decide : newFileFlags ≠ directoryFlags) source

private theorem cleanup_not_exclusive (run : RunDirectory.Owned) :
    RequestProgram (fun request => ¬ ExclusiveFile request) (RunDirectory.cleanup run) := by
  apply request_weaken (RunDirectory.cleanup_requests run)
  intro request source exclusive
  simp only [RunDirectory.CleanupRequest, exclusive.1] at source

private theorem readonly_not_exclusive {α : Type} {program : Filesystem.Program α}
    (source : RequestProgram NamespacePassive program) : RequestProgram (fun request => ¬ ExclusiveFile request) program :=
  request_weaken source (fun _ => passive_not_exclusive)

-- §FS-host-boundary.ownership: The actual validator policy open retains
-- its own acknowledged run creation and source-program operands. Setup,
-- cleanup and unknown-lifetime release cannot invent an exclusive writer.
theorem validator_exclusive_call {bundle : Validation.Bundle} {raw : ByteArray}
    {before : List Program.Event} {request : Request}
    (source : ValidatorMutation bundle raw before (.lost (.filesystem request))) (exclusive : ExclusiveFile request) :
    Nonempty (RunFileCall before request) := by
  cases source with
  | allocating active =>
    exact False.elim (selected_filesystem_profile (observed := none) create_not_exclusive active exclusive)
  | writing context inside active trace =>
    obtain ⟨events, active, projection⟩ := selected_filesystem_source (observed := none) active
    exact ⟨{
      directory := context.directory
      outside := []
      creating := context.allocating
      created := context.allocate
      kind := .validator raw
      inside := events
      active
      trace := by simpa only [ValidatorPrefixCuts.Allocated.events, List.nil_append, projection] using trace }⟩
  | cleaningFailedWrite context writing error written inside active trace =>
    exact False.elim (selected_filesystem_profile (observed := none) (cleanup_not_exclusive _) active exclusive)
  | cleaningObserved context inside reaped active trace =>
    exact False.elim (selected_filesystem_profile (observed := none) (cleanup_not_exclusive _) active exclusive)
  | releasingUnknown context inside unknown active trace =>
    exact False.elim (passive_not_exclusive (selected_filesystem_profile (observed := none) (validator_release_passive _) active) exclusive)

inductive RunExclusiveSite (request : GatewayWire.Request) (bundle : Validation.Bundle) (duration : Option Nat)
    (before : List Program.Event) (operation : Request) : Type 1 where
  | file (source : RunFileCall before operation)
  | publication (source : RunPublicationCall request bundle duration before (.lost (.filesystem operation)))

-- §FS-host-boundary.ownership: A run's actual exclusive open is a validator
-- policy writer, its request archive writer or the real publisher. Each
-- case retains the same completed allocation and current source prefix.
theorem run_exclusive_site {request : GatewayWire.Request} {bundle : Validation.Bundle} {duration : Option Nat}
    {before : List Program.Event} {operation : Request}
    (source : RunMutation request bundle duration before (.lost (.filesystem operation)))
    (exclusive : ExclusiveFile operation) : Nonempty (RunExclusiveSite request bundle duration before operation) := by
  cases source with
  | preparing source =>
    cases source with
    | validating context inside source trace =>
      obtain ⟨call⟩ := validator_exclusive_call source exclusive
      exact ⟨.file (call.prepend context.events trace)⟩
    | revalidating context inside source trace =>
      obtain ⟨call⟩ := validator_exclusive_call source exclusive
      exact ⟨.file (call.prepend context.events trace)⟩
  | allocating context inside active trace =>
    exact False.elim (selected_filesystem_profile (observed := none) create_not_exclusive active exclusive)
  | imaging context inside active trace =>
    obtain ⟨events, active, projection⟩ := selected_filesystem_source (observed := none) active
    exact ⟨.file {
      directory := context.directory
      outside := context.setup.events
      creating := context.allocating
      created := context.allocate
      kind := .image bundle (Image.entries (Snapshot.hex context.setup.random) bundle.identity
        (request.command == GatewayWire.checkCommand) request.fault context.setup.policy context.setup.frozen)
      inside := events
      active
      trace := by simpa only [RunPrefixCuts.Allocated.events, List.append_assoc, projection] using trace }⟩
  | dispatching context inside active trace =>
    exact False.elim (passive_not_exclusive (dispatch_namespace_passive (observed := none) _ _ _ _ _ _ _ _ active) exclusive)
  | cleaning context inside active trace =>
    have shape : cleanupRun context.imaged.allocated.directory context.input =
        if context.input.outcome.vmCleanup == "unknown" then
          Program.liftFilesystem (Validation.releaseDirectory context.imaged.allocated.directory)
        else Program.liftFilesystem (RunDirectory.cleanup context.imaged.allocated.directory) := rfl
    rw [shape] at active
    split at active
    · exact False.elim (passive_not_exclusive (selected_filesystem_profile (observed := none) (validator_release_passive _) active) exclusive)
    · exact False.elim (selected_filesystem_profile (observed := none) (cleanup_not_exclusive _) active exclusive)
  | publishing context inside active trace => exact ⟨.publication ⟨context, inside, active, trace⟩⟩

inductive EntryExclusiveSite (before : List Program.Event) (request : Request) : Type 1 where
  | file (source : RunFileCall before request)
  | publication (source : EntryPublicationCall before (.lost (.filesystem request)))

-- §FS-host-boundary.ownership: The full caller chooses these exclusive
-- file sources itself; no free source phase, run directory or publication
-- role is supplied at the raw filesystem boundary.
theorem entrypoint_exclusive_site {before : List Program.Event} {request : Request}
    (active : Program.Prefix Entrypoint.run (before ++ [.lost (.filesystem request)]))
    (exclusive : ExclusiveFile request) : Nonempty (EntryExclusiveSite before request) := by
  obtain ⟨entry⟩ := entrypoint_mutation_origin (observed := none) active (fun passive => passive_not_exclusive passive exclusive)
  have source := entry.source
  cases source with
  | validating context raw loading loaded inside active trace =>
    obtain ⟨source⟩ := validator_mutation_origin (observed := none) _ _ active
    obtain ⟨call⟩ := validator_exclusive_call source exclusive
    exact ⟨.file ((call.prepend (context.events ++ loading.map Program.filesystemEvent) trace).prepend
      entry.packet.events entry.trace)⟩
  | executing context inside command active trace =>
    obtain ⟨source⟩ := run_mutation_origin (observed := none) _ _ _ active (fun passive => passive_not_exclusive passive exclusive)
    obtain ⟨site⟩ := run_exclusive_site source exclusive
    cases site with
    | file call => exact ⟨.file ((call.prepend context.events trace).prepend entry.packet.events entry.trace)⟩
    | publication publication =>
      exact ⟨.publication ⟨entry.packet, entry.original, entry.effective, entry.duration, entry.accepted, entry.invocation,
        context, command, inside, publication, by
          simpa only [List.append_assoc] using entry.trace.trans (congrArg (entry.packet.events ++ ·) trace)⟩⟩

end LeanCage.Host.Kernel
