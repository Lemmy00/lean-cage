import FilesystemMarkerBindings.RunSource
import FilesystemAuthoritySources

namespace LeanCage.Host.Kernel
open Filesystem

structure RunCreationPrefix (before : List Program.Event) (request : Request) (observed : Option Reply) where
  context : List Program.Event
  inside : List (Request × Option Reply)
  active : Prefix RunDirectory.create (inside ++ [(request, observed)])
  trace : before = context ++ inside.map Program.filesystemPrefixEvent

def RunCreationPrefix.prepend {before outside : List Program.Event} {request : Request} {observed : Option Reply}
    (source : RunCreationPrefix before request observed) (context : List Program.Event)
    (trace : outside = context ++ before) : RunCreationPrefix outside request observed := {
  context := context ++ source.context
  inside := source.inside
  active := source.active
  trace := by simpa only [List.append_assoc] using trace.trans (congrArg (context ++ ·) source.trace) }

private theorem lifted_creation {before : List Program.Event} {request : Request} {observed : Option Reply}
    (active : Program.Prefix (Program.liftFilesystem RunDirectory.create)
      (before ++ [Program.filesystemPrefixEvent (request, observed)])) :
    Nonempty (RunCreationPrefix before request observed) := by
  obtain ⟨inside, source, trace⟩ := selected_filesystem_source active
  exact ⟨⟨[], inside, source, by simpa only [List.nil_append] using trace⟩⟩

private theorem cleanup_no_attribute (run : RunDirectory.Owned) :
    RequestProgram Publication.NoAttribute (RunDirectory.cleanup run) := by
  apply request_weaken (RunDirectory.cleanup_requests run)
  intro request source setting
  unfold RunDirectory.CleanupRequest at source
  rw [setting] at source
  exact source

private theorem image_no_attribute (fd : UInt64) (bundle : Validation.Bundle) (overlay : List Image.Entry) :
    RequestProgram Publication.NoAttribute (Image.create fd bundle overlay) := by
  unfold Image.create
  split
  · exact .pure _
  · apply request_bind (Publication.readOnly_no_attribute (Image.copyIdentified_readOnly _ _ _))
    intro base
    cases base with
    | error => exact .pure _
    | ok base =>
      apply RequestProgram.call (by intro impossible; cases impossible)
      intro reply
      dsimp only [Filesystem.Program.bind]
      split
      · exact .pure _
      · apply request_weaken (Image.contentClose_requests _ _ _)
        intro request source setting
        rcases source with writing | closing
        · rw [writing.1] at setting; cases setting
        · rw [closing] at setting; cases setting

private theorem publisher_no_private {α : Type} {program : Filesystem.Program α}
    (source : Publication.PublisherProgram program) :
    RequestProgram (fun request => request.op = .setAttribute → request.left ≠ PrivateNames.attributeName) program := by
  induction source with
  | pure => exact .pure _
  | call permitted following ih =>
    apply RequestProgram.call _ ih
    intro setting
    rcases permitted with renameOperation | safe
    · rw [renameOperation] at setting; cases setting
    · unfold Publication.SafeRequest at safe
      rw [setting] at safe
      rw [safe.1]
      decide

private theorem validator_private_marker {bundle : Validation.Bundle} {raw : ByteArray}
    {before : List Program.Event} {request : Request} {observed : Option Reply}
    (source : ValidatorMutation bundle raw before (Program.filesystemPrefixEvent (request, observed)))
    (setting : request.op = .setAttribute) : Nonempty (RunCreationPrefix before request observed) := by
  cases source with
  | allocating active => exact lifted_creation active
  | writing context inside active trace =>
    exact False.elim (selected_filesystem_profile (Publication.writeNew_no_attribute _ _ _ _) active setting)
  | cleaningFailedWrite context writing error written inside active trace =>
    exact False.elim (selected_filesystem_profile (cleanup_no_attribute _) active setting)
  | cleaningObserved context inside reaped active trace =>
    exact False.elim (selected_filesystem_profile (cleanup_no_attribute _) active setting)
  | releasingUnknown context inside unknown active trace =>
    exact False.elim (Publication.namespace_no_attribute _
      (selected_filesystem_profile (validator_release_passive _) active) setting)

private theorem run_private_marker {request : GatewayWire.Request} {bundle : Validation.Bundle} {duration : Option Nat}
    {before : List Program.Event} {operation : Request} {observed : Option Reply}
    (source : RunMutation request bundle duration before (Program.filesystemPrefixEvent (operation, observed)))
    (setting : operation.op = .setAttribute) (named : operation.left = PrivateNames.attributeName) :
    Nonempty (RunCreationPrefix before operation observed) := by
  cases source with
  | preparing source =>
    cases source with
    | validating context inside source trace =>
      obtain ⟨creation⟩ := validator_private_marker source setting
      exact ⟨creation.prepend context.events trace⟩
    | revalidating context inside source trace =>
      obtain ⟨creation⟩ := validator_private_marker source setting
      exact ⟨creation.prepend context.events trace⟩
  | allocating context inside active trace =>
    obtain ⟨creation⟩ := lifted_creation active
    exact ⟨creation.prepend context.events trace⟩
  | imaging context inside active trace =>
    exact False.elim (selected_filesystem_profile (image_no_attribute _ _ _) active setting)
  | dispatching context inside active trace =>
    exact False.elim (Publication.namespace_no_attribute _
      (dispatch_namespace_passive _ _ _ _ _ _ _ _ active) setting)
  | cleaning context inside active trace =>
    have same : cleanupRun context.imaged.allocated.directory context.input =
        if context.input.outcome.vmCleanup == "unknown" then
          Program.liftFilesystem (Validation.releaseDirectory context.imaged.allocated.directory)
        else Program.liftFilesystem (RunDirectory.cleanup context.imaged.allocated.directory) := rfl
    rw [same] at active
    split at active
    · exact False.elim (Publication.namespace_no_attribute _
        (selected_filesystem_profile (validator_release_passive _) active) setting)
    · exact False.elim (selected_filesystem_profile (cleanup_no_attribute _) active setting)
  | publishing context inside active trace =>
    exact False.elim (selected_filesystem_profile
      (publisher_no_private (Publication.publish_prefix_program _ _ _)) active setting named)

-- §FS-host-boundary.ownership: Every private setter has this actual run-creation source context.
theorem entrypoint_private_marker_call {before : List Program.Event} {request : Request} {observed : Option Reply}
    (active : Program.Prefix Entrypoint.run (before ++ [Program.filesystemPrefixEvent (request, observed)]))
    (setting : request.op = .setAttribute) (named : request.left = PrivateNames.attributeName) :
    Nonempty (RunCreationPrefix before request observed) := by
  have mutating : ¬ NamespacePassive request := fun passive => Publication.namespace_no_attribute _ passive setting
  obtain ⟨entry⟩ := entrypoint_mutation_origin active mutating
  have source := entry.source
  cases source with
  | validating context raw loading loaded inside active trace =>
    obtain ⟨source⟩ := validator_mutation_origin _ _ active
    obtain ⟨creation⟩ := validator_private_marker source setting
    exact ⟨(creation.prepend (context.events ++ loading.map Program.filesystemEvent) trace).prepend
      entry.packet.events entry.trace⟩
  | executing context inside command active trace =>
    obtain ⟨source⟩ := run_mutation_origin _ _ _ active mutating
    obtain ⟨creation⟩ := run_private_marker source setting named
    exact ⟨(creation.prepend context.events trace).prepend entry.packet.events entry.trace⟩

end LeanCage.Host.Kernel
