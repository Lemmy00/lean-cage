import FilesystemMarkerBindings.Invocation
import FilesystemMkdirSources

namespace LeanCage.Host.Kernel
open Filesystem

def NoMkdir (request : Request) : Prop := request.op ≠ .mkdirAt

private theorem passive_no_mkdir {request : Request} (passive : NamespacePassive request) : NoMkdir request := by
  intro mkdir
  unfold NamespacePassive at passive
  rw [mkdir] at passive
  exact passive

private theorem write_new_no_mkdir (parent : UInt64) (name bytes : ByteArray) (mode : UInt64) :
    RequestProgram NoMkdir (writeNew parent name bytes mode) := by
  unfold writeNew
  split
  · exact .pure _
  · apply RequestProgram.call (by intro impossible; cases impossible)
    intro reply
    split
    · exact .pure _
    · apply request_bind (request_weaken (write_loop_namespace_passive _ _ _ _) (fun _ => passive_no_mkdir))
      intro result
      apply RequestProgram.call (by intro impossible; cases impossible)
      intro closed
      cases result with
      | error => exact .pure _
      | ok value => dsimp only; split <;> exact .pure _

private theorem cleanup_no_mkdir (run : RunDirectory.Owned) : RequestProgram NoMkdir (RunDirectory.cleanup run) := by
  apply request_weaken (RunDirectory.cleanup_requests run)
  intro request source mkdir
  unfold RunDirectory.CleanupRequest at source
  rw [mkdir] at source
  exact source

private theorem image_no_mkdir (fd : UInt64) (bundle : Validation.Bundle) (overlay : List Image.Entry) :
    RequestProgram NoMkdir (Image.create fd bundle overlay) := by
  unfold Image.create
  split
  · exact .pure _
  · apply request_bind (request_weaken
      (read_only_namespace_passive (Image.copyIdentified_readOnly _ _ _)) (fun _ => passive_no_mkdir))
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
        intro request source mkdir
        rcases source with writing | closing
        · rw [writing.1] at mkdir; cases mkdir
        · rw [closing] at mkdir; cases mkdir

private theorem lifted_creation {before : List Program.Event} {request : Request} {observed : Option Reply}
    (source : Program.Prefix (Program.liftFilesystem RunDirectory.create)
      (before ++ [Program.filesystemPrefixEvent (request, observed)])) :
    Nonempty (RunCreationPrefix before request observed) := by
  obtain ⟨inside, source, trace⟩ := selected_filesystem_source source
  exact ⟨⟨[], inside, source, by simpa only [List.nil_append] using trace⟩⟩

private theorem validator_mkdir_creation {bundle : Validation.Bundle} {raw : ByteArray}
    {before : List Program.Event} {request : Request} {observed : Option Reply}
    (source : ValidatorMutation bundle raw before (Program.filesystemPrefixEvent (request, observed)))
    (mkdir : request.op = .mkdirAt) : Nonempty (RunCreationPrefix before request observed) := by
  cases source with
  | allocating active => exact lifted_creation active
  | writing context inside active trace =>
    exact False.elim (selected_filesystem_profile (write_new_no_mkdir _ _ _ _) active mkdir)
  | cleaningFailedWrite context writing error written inside active trace =>
    exact False.elim (selected_filesystem_profile (cleanup_no_mkdir _) active mkdir)
  | cleaningObserved context inside reaped active trace =>
    exact False.elim (selected_filesystem_profile (cleanup_no_mkdir _) active mkdir)
  | releasingUnknown context inside unknown active trace =>
    exact False.elim (passive_no_mkdir (selected_filesystem_profile (validator_release_passive _) active) mkdir)

inductive RunMkdirSite (request : GatewayWire.Request) (bundle : Validation.Bundle) (duration : Option Nat)
    (before : List Program.Event) (operation : Request) (observed : Option Reply) : Type 1 where
  | creating (source : RunCreationPrefix before operation observed)
  | publishing (source : RunPublicationCall request bundle duration before
      (Program.filesystemPrefixEvent (operation, observed)))

theorem run_mkdir_site {request : GatewayWire.Request} {bundle : Validation.Bundle} {duration : Option Nat}
    {before : List Program.Event} {operation : Request} {observed : Option Reply}
    (source : RunMutation request bundle duration before (Program.filesystemPrefixEvent (operation, observed)))
    (mkdir : operation.op = .mkdirAt) : Nonempty (RunMkdirSite request bundle duration before operation observed) := by
  cases source with
  | preparing source =>
    cases source with
    | validating context inside source trace =>
      obtain ⟨creation⟩ := validator_mkdir_creation source mkdir
      exact ⟨.creating (creation.prepend context.events trace)⟩
    | revalidating context inside source trace =>
      obtain ⟨creation⟩ := validator_mkdir_creation source mkdir
      exact ⟨.creating (creation.prepend context.events trace)⟩
  | allocating context inside active trace =>
    obtain ⟨creation⟩ := lifted_creation active
    exact ⟨.creating (creation.prepend context.events trace)⟩
  | imaging context inside active trace => exact False.elim (selected_filesystem_profile (image_no_mkdir _ _ _) active mkdir)
  | dispatching context inside active trace =>
    exact False.elim (passive_no_mkdir (dispatch_namespace_passive _ _ _ _ _ _ _ _ active) mkdir)
  | cleaning context inside active trace =>
    have same : cleanupRun context.imaged.allocated.directory context.input =
        if context.input.outcome.vmCleanup == "unknown" then
          Program.liftFilesystem (Validation.releaseDirectory context.imaged.allocated.directory)
        else Program.liftFilesystem (RunDirectory.cleanup context.imaged.allocated.directory) := rfl
    rw [same] at active
    split at active
    · exact False.elim (passive_no_mkdir (selected_filesystem_profile (validator_release_passive _) active) mkdir)
    · exact False.elim (selected_filesystem_profile (cleanup_no_mkdir _) active mkdir)
  | publishing context inside active trace => exact ⟨.publishing ⟨context, inside, active, trace⟩⟩

inductive HostMkdirSite (before : List Program.Event) (request : Request) (observed : Option Reply) : Type 1 where
  | creating (source : RunCreationPrefix before request observed)
  | publishing (source : EntryPublicationCall before (Program.filesystemPrefixEvent (request, observed)))

-- §FS-host-boundary.ownership: Every mkdir originates in real run setup or actual publication.
theorem entrypoint_mkdir_site {before : List Program.Event} {request : Request} {observed : Option Reply}
    (active : Program.Prefix Entrypoint.run (before ++ [Program.filesystemPrefixEvent (request, observed)]))
    (mkdir : request.op = .mkdirAt) : Nonempty (HostMkdirSite before request observed) := by
  have mutating : ¬ NamespacePassive request := fun passive => passive_no_mkdir passive mkdir
  obtain ⟨entry⟩ := entrypoint_mutation_origin active mutating
  have source := entry.source
  cases source with
  | validating context raw loading loaded inside active trace =>
    obtain ⟨source⟩ := validator_mutation_origin _ _ active
    obtain ⟨creation⟩ := validator_mkdir_creation source mkdir
    exact ⟨.creating ((creation.prepend (context.events ++ loading.map Program.filesystemEvent) trace).prepend
      entry.packet.events entry.trace)⟩
  | executing context inside command active trace =>
    obtain ⟨source⟩ := run_mutation_origin _ _ _ active mutating
    obtain ⟨site⟩ := run_mkdir_site source mkdir
    cases site with
    | creating creation =>
      exact ⟨.creating ((creation.prepend context.events trace).prepend entry.packet.events entry.trace)⟩
    | publishing publication =>
      exact ⟨.publishing ⟨entry.packet, entry.original, entry.effective, entry.duration, entry.accepted,
        entry.invocation, context, command, inside, publication, by
          simpa only [List.append_assoc] using
            (entry.trace.trans (congrArg (entry.packet.events ++ ·) trace))⟩⟩

theorem selected_mkdir_site {kernel : Contract} {runtime : ActorRuntime kernel}
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply} (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) (mkdir : request.op = .mkdirAt) :
    Nonempty (HostMkdirSite engine.events request observed) :=
  entrypoint_mkdir_site (selected_source_prefix journal selected action present) mkdir

end LeanCage.Host.Kernel
