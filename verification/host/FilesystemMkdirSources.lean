import FilesystemSourceOrigins

namespace LeanCage.Host.Kernel
open Filesystem

def PrivateDirectoryMode (request : Request) : Prop :=
  request.op = .mkdirAt → request.second = 448

theorem passive_private_directory_mode {request : Request} (source : NamespacePassive request) :
    PrivateDirectoryMode request := by
  intro mkdir
  unfold NamespacePassive at source
  rw [mkdir] at source
  exact False.elim source

theorem publication_private_directory_mode {request : Request} (source : Publication.SafeRequest request) :
    PrivateDirectoryMode request := by
  intro mkdir
  unfold Publication.SafeRequest at source
  rw [mkdir] at source
  exact source

theorem publication_private_directory_program {α : Type} {program : Filesystem.Program α}
    (source : Publication.PublisherProgram program) : RequestProgram PrivateDirectoryMode program := by
  induction source with
  | pure => exact .pure _
  | call permitted following ih =>
    apply RequestProgram.call _ ih
    rcases permitted with rename | safe
    · intro mkdir; rw [rename] at mkdir; cases mkdir
    · exact publication_private_directory_mode safe

theorem run_creation_private_directory_program : RequestProgram PrivateDirectoryMode RunDirectory.create := by
  apply request_weaken RunDirectory.create_requests
  intro request source mkdir
  unfold RunDirectory.DirectoryRequest at source
  rw [mkdir] at source
  exact source

theorem run_cleanup_private_directory_program (run : RunDirectory.Owned) :
    RequestProgram PrivateDirectoryMode (RunDirectory.cleanup run) := by
  apply request_weaken (RunDirectory.cleanup_requests run)
  intro request source mkdir
  unfold RunDirectory.CleanupRequest at source
  rw [mkdir] at source
  exact False.elim source

theorem safe_private_directory_program {α : Type} {program : Filesystem.Program α} (source : Publication.SafeProgram program) :
    RequestProgram PrivateDirectoryMode program :=
  publication_private_directory_program (Publication.publisher_safe source)

theorem image_private_directory_program (run : UInt64) (bundle : Validation.Bundle) (overlay : List Image.Entry) :
    RequestProgram PrivateDirectoryMode (Image.create run bundle overlay) := by
  unfold Image.create
  split
  · exact .pure _
  · apply request_bind (request_weaken
      (read_only_namespace_passive (Image.copyIdentified_readOnly _ _ _)) (fun _ => passive_private_directory_mode))
    intro copied
    cases copied with
    | error => exact .pure _
    | ok base =>
      apply RequestProgram.call (by intro mkdir; cases mkdir)
      intro reply
      dsimp only [Filesystem.Program.bind]
      split
      · exact .pure _
      · apply request_weaken (Image.contentClose_requests _ _ _)
        intro request source mkdir
        rcases source with writing | closing
        · rw [writing.1] at mkdir; cases mkdir
        · rw [closing] at mkdir; cases mkdir

theorem cleanup_private_directory_mode (run : RunDirectory.Owned) (input : Publication.Input)
    {before : List Program.Event} {request : Request} {observed : Option Reply}
    (source : Program.Prefix (cleanupRun run input)
      (before ++ [Program.filesystemPrefixEvent (request, observed)])) : PrivateDirectoryMode request := by
  have same : cleanupRun run input =
      if input.outcome.vmCleanup == "unknown" then Program.liftFilesystem (Validation.releaseDirectory run)
      else Program.liftFilesystem (RunDirectory.cleanup run) := rfl
  rw [same] at source
  split at source
  · exact passive_private_directory_mode (selected_filesystem_profile (validator_release_passive run) source)
  · exact selected_filesystem_profile (run_cleanup_private_directory_program run) source

theorem validator_private_directory_mode {bundle : Validation.Bundle} {raw : ByteArray}
    {before : List Program.Event} {request : Request} {observed : Option Reply}
    (source : ValidatorMutation bundle raw before (Program.filesystemPrefixEvent (request, observed))) :
    PrivateDirectoryMode request := by
  cases source with
  | allocating active => exact selected_filesystem_profile run_creation_private_directory_program active
  | writing context inside active trace =>
    exact selected_filesystem_profile (safe_private_directory_program (Publication.writeNew_safe _ _ _ _)) active
  | cleaningFailedWrite context writing error written inside active trace =>
    exact selected_filesystem_profile (run_cleanup_private_directory_program _) active
  | cleaningObserved context inside reaped active trace =>
    exact selected_filesystem_profile (run_cleanup_private_directory_program _) active
  | releasingUnknown context inside unknown active trace =>
    exact passive_private_directory_mode (selected_filesystem_profile (validator_release_passive _) active)

theorem run_private_directory_mode {request : GatewayWire.Request} {bundle : Validation.Bundle}
    {duration : Option Nat} {before : List Program.Event} {operation : Request} {observed : Option Reply}
    (source : RunMutation request bundle duration before (Program.filesystemPrefixEvent (operation, observed))) :
    PrivateDirectoryMode operation := by
  cases source with
  | preparing source =>
    cases source with
    | validating context inside source trace => exact validator_private_directory_mode source
    | revalidating context inside source trace => exact validator_private_directory_mode source
  | allocating context inside active trace => exact selected_filesystem_profile run_creation_private_directory_program active
  | imaging context inside active trace => exact selected_filesystem_profile (image_private_directory_program _ _ _) active
  | dispatching context inside active trace =>
    exact passive_private_directory_mode (dispatch_namespace_passive _ _ _ _ _ _ _ _ active)
  | cleaning context inside active trace => exact cleanup_private_directory_mode _ _ active
  | publishing context inside active trace =>
    exact selected_filesystem_profile (publication_private_directory_program (Publication.publish_prefix_program _ _ _)) active

-- §FS-host-boundary.ownership: Every actual directory creation uses the checked private mode.
theorem entrypoint_private_directory_mode {before : List Program.Event} {request : Request} {observed : Option Reply}
    (source : Program.Prefix Entrypoint.run (before ++ [Program.filesystemPrefixEvent (request, observed)])) :
    PrivateDirectoryMode request := by
  intro mkdir
  have mutating : ¬ NamespacePassive request := by
    intro passive
    unfold NamespacePassive at passive
    rw [mkdir] at passive
    exact passive
  obtain ⟨entry⟩ := entrypoint_mutation_origin source mutating
  have active := entry.source
  cases active with
  | validating context raw loading loaded inside active trace =>
    obtain ⟨role⟩ := validator_mutation_origin _ _ active
    exact validator_private_directory_mode role mkdir
  | executing context inside command active trace =>
    obtain ⟨role⟩ := run_mutation_origin _ _ _ active mutating
    exact run_private_directory_mode role mkdir

-- §FS-host-boundary.acceptance: The primitive's user-mkdir condition has a real producer.
theorem selected_private_directory_mode {kernel : Contract} {runtime : ActorRuntime kernel}
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply}
    (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) : PrivateDirectoryMode request :=
  entrypoint_private_directory_mode (selected_source_prefix journal selected action present)

end LeanCage.Host.Kernel
