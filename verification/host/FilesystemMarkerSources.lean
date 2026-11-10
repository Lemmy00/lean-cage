import PublicationMarkerProofs
import FilesystemHandoff

namespace LeanCage.Host.Kernel
open Filesystem

-- §FS-host-boundary.publication: Private-directory tags cannot masquerade as publication tags.
def NoPublicationMarker (request : Request) : Prop :=
  request.op = .setAttribute → request.left ≠ Publication.attributeName

theorem no_attribute_no_marker {request : Request} (safe : Publication.NoAttribute request) :
    NoPublicationMarker request := fun marked => False.elim (safe marked)

theorem run_creation_no_marker : RequestProgram NoPublicationMarker RunDirectory.create := by
  apply request_weaken RunDirectory.create_requests
  intro request source marked
  unfold RunDirectory.DirectoryRequest at source
  rw [marked] at source
  rw [source.1]
  decide

theorem run_cleanup_no_marker (run : RunDirectory.Owned) :
    RequestProgram NoPublicationMarker (RunDirectory.cleanup run) := by
  apply request_weaken (RunDirectory.cleanup_requests run)
  intro request source marked
  unfold RunDirectory.CleanupRequest at source
  rw [marked] at source
  exact False.elim source

theorem image_no_marker (runFd : UInt64) (bundle : Validation.Bundle) (overlay : List Image.Entry) :
    RequestProgram NoPublicationMarker (Image.create runFd bundle overlay) := by
  unfold Image.create
  split
  · exact .pure _
  · apply request_bind (request_weaken (Publication.readOnly_no_attribute
      (Image.copyIdentified_readOnly _ _ _)) (fun _ => no_attribute_no_marker))
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
        intro request source marked
        rcases source with writing | closing
        · rw [writing.1] at marked; cases marked
        · rw [closing] at marked; cases marked

theorem cleanup_no_marker (run : RunDirectory.Owned) (input : Publication.Input)
    {before : List Program.Event} {request : Request} {observed : Option Reply}
    (active : Program.Prefix (cleanupRun run input)
      (before ++ [Program.filesystemPrefixEvent (request, observed)])) : NoPublicationMarker request := by
  have same : cleanupRun run input =
      if input.outcome.vmCleanup == "unknown" then Program.liftFilesystem (Validation.releaseDirectory run)
      else Program.liftFilesystem (RunDirectory.cleanup run) := rfl
  rw [same] at active
  split at active
  · exact no_attribute_no_marker (Publication.namespace_no_attribute _
      (selected_filesystem_profile (validator_release_passive run) active))
  · exact selected_filesystem_profile (run_cleanup_no_marker run) active

theorem validator_mutation_no_marker {bundle : Validation.Bundle} {raw : ByteArray}
    {before : List Program.Event} {request : Request} {observed : Option Reply}
    (source : ValidatorMutation bundle raw before (Program.filesystemPrefixEvent (request, observed))) :
    NoPublicationMarker request := by
  cases source with
  | allocating active => exact selected_filesystem_profile run_creation_no_marker active
  | writing context inside active trace =>
    exact no_attribute_no_marker (selected_filesystem_profile (Publication.writeNew_no_attribute _ _ _ _) active)
  | cleaningFailedWrite context writing error written inside active trace =>
    exact selected_filesystem_profile (run_cleanup_no_marker _) active
  | cleaningObserved context inside reaped active trace =>
    exact selected_filesystem_profile (run_cleanup_no_marker _) active
  | releasingUnknown context inside unknown active trace =>
    exact no_attribute_no_marker (Publication.namespace_no_attribute _
      (selected_filesystem_profile (validator_release_passive _) active))

theorem run_marker_publication (request : GatewayWire.Request) (bundle : Validation.Bundle) (override : Option Nat)
    {before : List Program.Event} {operation : Request} {observed : Option Reply}
    (active : Program.Prefix (executeRun request bundle override).run
      (before ++ [Program.filesystemPrefixEvent (operation, observed)]))
    (marked : operation.op = .setAttribute) (named : operation.left = Publication.attributeName) :
    Nonempty (RunPublicationCall request bundle override before (Program.filesystemPrefixEvent (operation, observed))) := by
  have mutating : ¬ NamespacePassive operation := fun passive =>
    Publication.namespace_no_attribute operation passive marked
  obtain ⟨source⟩ := run_mutation_origin request bundle override active mutating
  cases source with
  | preparing source =>
    cases source with
    | validating context inside source trace => exact False.elim (validator_mutation_no_marker source marked named)
    | revalidating context inside source trace => exact False.elim (validator_mutation_no_marker source marked named)
  | allocating context inside active trace =>
    exact False.elim (selected_filesystem_profile run_creation_no_marker active marked named)
  | imaging context inside active trace =>
    exact False.elim (selected_filesystem_profile (image_no_marker _ _ _) active marked named)
  | dispatching context inside active trace =>
    exact False.elim (mutating (dispatch_namespace_passive _ _ _ _ _ _ _ _ active))
  | cleaning context inside active trace => exact False.elim (cleanup_no_marker _ _ active marked named)
  | publishing context inside active trace => exact ⟨⟨context, inside, active, trace⟩⟩

-- §FS-host-boundary.publication: Marker exposure is selected by the actual authenticated caller.
theorem entrypoint_marker_publication {before : List Program.Event} {operation : Request} {observed : Option Reply}
    (active : Program.Prefix Entrypoint.run (before ++ [Program.filesystemPrefixEvent (operation, observed)]))
    (marked : operation.op = .setAttribute) (named : operation.left = Publication.attributeName) :
    Nonempty (EntryPublicationCall before (Program.filesystemPrefixEvent (operation, observed))) := by
  obtain ⟨entry⟩ := entrypoint_mutation_origin active
    (fun passive => Publication.namespace_no_attribute operation passive marked)
  have source := entry.source
  cases source with
  | validating context raw loading loaded inside active trace =>
    obtain ⟨source⟩ := validator_mutation_origin _ _ active
    exact False.elim (validator_mutation_no_marker source marked named)
  | executing context inside command active trace =>
    obtain ⟨run⟩ := run_marker_publication _ _ _ active marked named
    exact ⟨⟨entry.packet, entry.original, entry.effective, entry.duration, entry.accepted, entry.invocation,
      context, command, inside, run, by
        simpa only [List.append_assoc] using (entry.trace.trans (congrArg (entry.packet.events ++ ·) trace))⟩⟩

structure HostMarkerCall (before : List Program.Event) (operation : Request) (observed : Option Reply) where
  invocation : EntryPublicationCall before (Program.filesystemPrefixEvent (operation, observed))
  earlier : List (Request × Option Reply)
  source : Publication.PublishedMarkerCall invocation.effective invocation.authenticated.bundle
    invocation.run.context.dispatched.input earlier operation
  projection : invocation.run.inside = earlier.map Program.filesystemPrefixEvent

theorem entrypoint_marker_call {before : List Program.Event} {operation : Request} {observed : Option Reply}
    (active : Program.Prefix Entrypoint.run (before ++ [Program.filesystemPrefixEvent (operation, observed)]))
    (marked : operation.op = .setAttribute) (named : operation.left = Publication.attributeName) :
    Nonempty (HostMarkerCall before operation observed) := by
  obtain ⟨invocation⟩ := entrypoint_marker_publication active marked named
  obtain ⟨earlier, source, projection⟩ := selected_filesystem_source invocation.run.active
  obtain ⟨marker⟩ := Publication.publish_marker_call _ _ _ source marked
  exact ⟨⟨invocation, earlier, marker, projection⟩⟩

-- §FS-host-boundary.acceptance: This source receipt is bound to this actual global marker tick.
theorem selected_publisher_marker {kernel : Contract} {runtime : ActorRuntime kernel}
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply}
    (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine)
    (marked : request.op = .setAttribute) (named : request.left = Publication.attributeName) :
    Nonempty (HostMarkerCall engine.events request observed) :=
  entrypoint_marker_call (selected_source_prefix journal selected action present) marked named

theorem completed_filesystem_events (events : List (Request × Reply)) :
    (Publication.completed events).map Program.filesystemPrefixEvent = events.map Program.filesystemEvent := by
  simp only [Publication.completed, List.map_map]
  rfl

def HostMarkerCall.context {before : List Program.Event} {operation : Request} {observed : Option Reply}
    (source : HostMarkerCall before operation observed) : List Program.Event :=
  source.invocation.packet.events ++ source.invocation.authenticated.events ++ source.invocation.run.context.events ++
    (source.source.identifying ++ source.source.selecting ++ source.source.source.displaying ++
      source.source.source.selecting ++ source.source.source.creating ++
      source.source.source.marker.hashing).map Program.filesystemEvent

-- §FS-host-boundary.publication: The exact completed MAC transcript is inside the caller prefix.
theorem marker_authentication_trace {before : List Program.Event} {operation : Request} {observed : Option Reply}
    (source : HostMarkerCall before operation observed) :
    before = source.context ++ source.source.source.marker.authenticating.map Program.filesystemEvent ++
      source.source.source.marker.filling.map Program.filesystemEvent := by
  conv =>
    lhs
    rw [source.invocation.trace, source.invocation.run.trace, source.projection, source.source.trace,
      source.source.source.trace, source.source.source.marker.trace]
  simp only [List.map_append, completed_filesystem_events, HostMarkerCall.context, List.append_assoc]

end LeanCage.Host.Kernel
