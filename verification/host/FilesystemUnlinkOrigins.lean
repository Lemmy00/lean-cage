import FilesystemMkdirOrigins
import FilesystemPublicationContentProfile

namespace LeanCage.Host.Kernel
open Filesystem

private theorem passive_no_unlink {request : Request} (passive : NamespacePassive request) : request.op ≠ .unlinkAt := by
  intro removing
  unfold NamespacePassive at passive
  rw [removing] at passive
  exact passive

private theorem write_new_no_unlink (parent : UInt64) (name bytes : ByteArray) (mode : UInt64) :
    RequestProgram (fun request => request.op ≠ .unlinkAt) (writeNew parent name bytes mode) :=
  request_weaken (writeNew_nondestructive _ _ _ _) (fun _ safe removing => safe (.inl removing))

private theorem image_no_unlink (fd : UInt64) (bundle : Validation.Bundle) (overlay : List Image.Entry) :
    RequestProgram (fun request => request.op ≠ .unlinkAt) (Image.create fd bundle overlay) := by
  unfold Image.create
  split
  · exact .pure _
  · apply request_bind (request_weaken (read_only_namespace_passive (Image.copyIdentified_readOnly _ _ _))
      (fun _ => passive_no_unlink))
    intro base
    cases base with
    | error => exact .pure _
    | ok base =>
      apply RequestProgram.call (by intro invalid; cases invalid)
      intro reply
      dsimp only [Filesystem.Program.bind]
      split
      · exact .pure _
      · apply request_weaken (Image.contentClose_requests _ _ _)
        intro operation role removing
        rcases role with writing | closing
        · rw [writing.1] at removing; cases removing
        · rw [closing] at removing; cases removing

-- §FS-host-boundary.ownership: Each run-root cleanup retains its real allocation
-- and prior write/spawn/reap or VM observation. A lost or unknown child status
-- cannot manufacture a removal branch; no cleanup-success result is required.
inductive RunCleanupOrigin : List Program.Event → Request → Option Reply → Type 1 where
  | creating {before : List Program.Event} {request : Request} {observed : Option Reply}
      (source : RunCreationPrefix before request observed) : RunCleanupOrigin before request observed
  | failedWrite {before : List Program.Event} {request : Request} {observed : Option Reply}
      (raw : ByteArray) (context : ValidatorPrefixCuts.Allocated)
      (writing : List (Request × Reply)) (error : Failure)
      (written : Returns (context.writeProgram raw) writing (.error error))
      (inside : List Program.Event)
      (active : Program.Prefix (Program.liftFilesystem (RunDirectory.cleanup context.directory))
        (inside ++ [Program.filesystemPrefixEvent (request, observed)]))
      (trace : before = context.events ++ writing.map Program.filesystemEvent ++ inside) :
      RunCleanupOrigin before request observed
  | observedChild {before : List Program.Event} {request : Request} {observed : Option Reply}
      (bundle : Validation.Bundle) (raw : ByteArray) (context : ValidatorPrefixCuts.Observed bundle raw)
      (reaped : context.result.reaped = true) (inside : List Program.Event)
      (active : Program.Prefix (Program.liftFilesystem
        (RunDirectory.cleanup context.spawned.written.allocated.directory))
        (inside ++ [Program.filesystemPrefixEvent (request, observed)]))
      (trace : before = context.events ++ inside) : RunCleanupOrigin before request observed
  | running {before : List Program.Event} {request : Request} {observed : Option Reply}
      (caller : GatewayWire.Request) (bundle : Validation.Bundle) (duration : Option Nat)
      (context : RunPrefixCuts.Dispatched caller bundle duration)
      (known : (context.input.outcome.vmCleanup == "unknown") = false) (inside : List Program.Event)
      (active : Program.Prefix (Program.liftFilesystem (RunDirectory.cleanup context.imaged.allocated.directory))
        (inside ++ [Program.filesystemPrefixEvent (request, observed)]))
      (trace : before = context.events ++ inside) : RunCleanupOrigin before request observed
  | prepend {before inside : List Program.Event} {request : Request} {observed : Option Reply}
      (source : RunCleanupOrigin inside request observed)
      (context : List Program.Event) (trace : before = context ++ inside) : RunCleanupOrigin before request observed

private theorem creation_unlink_origin {before : List Program.Event} {request : Request} {observed : Option Reply}
    (active : Program.Prefix (Program.liftFilesystem RunDirectory.create)
      (before ++ [Program.filesystemPrefixEvent (request, observed)])) : Nonempty (RunCleanupOrigin before request observed) := by
  obtain ⟨inside, source, trace⟩ := selected_filesystem_source active
  exact ⟨.creating ⟨[], inside, source, by simpa only [List.nil_append] using trace⟩⟩

private theorem validator_unlink_origin {bundle : Validation.Bundle} {raw : ByteArray}
    {before : List Program.Event} {request : Request} {observed : Option Reply}
    (source : ValidatorMutation bundle raw before (Program.filesystemPrefixEvent (request, observed)))
    (removing : request.op = .unlinkAt) : Nonempty (RunCleanupOrigin before request observed) := by
  cases source with
  | allocating active => exact creation_unlink_origin active
  | writing context inside active trace =>
    exact False.elim (selected_filesystem_profile (write_new_no_unlink _ _ _ _) active removing)
  | cleaningFailedWrite context writing error written inside active trace =>
    exact ⟨.failedWrite raw context writing error written inside active trace⟩
  | cleaningObserved context inside reaped active trace => exact ⟨.observedChild bundle raw context reaped inside active trace⟩
  | releasingUnknown context inside unknown active trace =>
    exact False.elim (passive_no_unlink (selected_filesystem_profile (validator_release_passive _) active) removing)

inductive RunUnlinkSite (caller : GatewayWire.Request) (bundle : Validation.Bundle) (duration : Option Nat)
    (before : List Program.Event) (request : Request) (observed : Option Reply) : Type 1 where
  | cleanup (source : RunCleanupOrigin before request observed)
  | publication (source : RunPublicationCall caller bundle duration before (Program.filesystemPrefixEvent (request, observed)))

private theorem run_unlink_site {caller : GatewayWire.Request} {bundle : Validation.Bundle} {duration : Option Nat}
    {before : List Program.Event} {request : Request} {observed : Option Reply}
    (source : RunMutation caller bundle duration before (Program.filesystemPrefixEvent (request, observed)))
    (removing : request.op = .unlinkAt) : Nonempty (RunUnlinkSite caller bundle duration before request observed) := by
  cases source with
  | preparing source =>
    cases source with
    | validating context inside active trace =>
      obtain ⟨cleanup⟩ := validator_unlink_origin active removing
      exact ⟨.cleanup (.prepend cleanup context.events trace)⟩
    | revalidating context inside active trace =>
      obtain ⟨cleanup⟩ := validator_unlink_origin active removing
      exact ⟨.cleanup (.prepend cleanup context.events trace)⟩
  | allocating context inside active trace =>
    obtain ⟨creating⟩ := creation_unlink_origin active
    exact ⟨.cleanup (.prepend creating context.events trace)⟩
  | imaging context inside active trace => exact False.elim (selected_filesystem_profile (image_no_unlink _ _ _) active removing)
  | dispatching context inside active trace =>
    exact False.elim (passive_no_unlink (dispatch_namespace_passive _ _ _ _ _ _ _ _ active) removing)
  | cleaning context inside active trace =>
    have same : cleanupRun context.imaged.allocated.directory context.input =
        if context.input.outcome.vmCleanup == "unknown" then
          Program.liftFilesystem (Validation.releaseDirectory context.imaged.allocated.directory)
        else Program.liftFilesystem (RunDirectory.cleanup context.imaged.allocated.directory) := rfl
    rw [same] at active
    split at active
    · exact False.elim (passive_no_unlink (selected_filesystem_profile (validator_release_passive _) active) removing)
    · rename_i known
      exact ⟨.cleanup (.running caller bundle duration context (Bool.eq_false_iff.mpr known) inside active trace)⟩
  | publishing context inside active trace => exact ⟨.publication ⟨context, inside, active, trace⟩⟩

inductive HostUnlinkSite (before : List Program.Event) (request : Request) (observed : Option Reply) : Type 1 where
  | cleanup (source : RunCleanupOrigin before request observed)
  | publication (source : EntryPublicationCall before (Program.filesystemPrefixEvent (request, observed)))

-- §FS-host-boundary.ownership: The whole real entrypoint classifies every unlink
-- as actual run/validator cleanup or the one publication invocation. This is a
-- source producer for the cumulative fold, never a supplied safe-caller label.
theorem entrypoint_unlink_site {before : List Program.Event} {request : Request} {observed : Option Reply}
    (source : Program.Prefix Entrypoint.run (before ++ [Program.filesystemPrefixEvent (request, observed)]))
    (removing : request.op = .unlinkAt) : Nonempty (HostUnlinkSite before request observed) := by
  have mutating : ¬ NamespacePassive request := fun passive => passive_no_unlink passive removing
  obtain ⟨entry⟩ := entrypoint_mutation_origin source mutating
  have active := entry.source
  cases active with
  | validating context raw loading loaded inside active trace =>
    obtain ⟨validator⟩ := validator_mutation_origin _ _ active
    obtain ⟨cleanup⟩ := validator_unlink_origin validator removing
    exact ⟨.cleanup (.prepend (.prepend cleanup (context.events ++ loading.map Program.filesystemEvent) trace)
      entry.packet.events entry.trace)⟩
  | executing context inside command active trace =>
    obtain ⟨running⟩ := run_mutation_origin _ _ _ active mutating
    obtain ⟨site⟩ := run_unlink_site running removing
    cases site with
    | cleanup cleanup => exact ⟨.cleanup (.prepend (.prepend cleanup context.events trace) entry.packet.events entry.trace)⟩
    | publication publication =>
      exact ⟨.publication ⟨entry.packet, entry.original, entry.effective, entry.duration, entry.accepted,
        entry.invocation, context, command, inside, publication, by
          simpa only [List.append_assoc] using entry.trace.trans (congrArg (entry.packet.events ++ ·) trace)⟩⟩

end LeanCage.Host.Kernel
