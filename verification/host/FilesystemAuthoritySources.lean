import FilesystemMetadata
import FilesystemSourceOrigins

namespace LeanCage.Host.Kernel
open Filesystem

theorem passive_authority_safe {request : Request} (source : NamespacePassive request) :
    AuthoritySafeRequest request := by
  intro setting
  unfold NamespacePassive at source
  rw [setting] at source
  exact False.elim source

theorem publication_authority_safe {request : Request} (source : Publication.SafeRequest request) :
    AuthoritySafeRequest request := by
  intro setting
  unfold Publication.SafeRequest at source
  rw [setting] at source
  exact .inr source.1

theorem publication_authority_program {α : Type} {program : Filesystem.Program α}
    (source : Publication.PublisherProgram program) : RequestProgram AuthoritySafeRequest program := by
  induction source with
  | pure => exact .pure _
  | call permitted following ih =>
    apply RequestProgram.call _ ih
    rcases permitted with rename | safe
    · intro setting; rw [rename] at setting; cases setting
    · exact publication_authority_safe safe

theorem run_creation_authority_program : RequestProgram AuthoritySafeRequest RunDirectory.create := by
  apply request_weaken RunDirectory.create_requests
  intro request source setting
  unfold RunDirectory.DirectoryRequest at source
  rw [setting] at source
  exact .inl source.1

theorem run_cleanup_authority_program (run : RunDirectory.Owned) :
    RequestProgram AuthoritySafeRequest (RunDirectory.cleanup run) := by
  apply request_weaken (RunDirectory.cleanup_requests run)
  intro request source setting
  unfold RunDirectory.CleanupRequest at source
  rw [setting] at source
  exact False.elim source

theorem safe_authority_program {α : Type} {program : Filesystem.Program α} (source : Publication.SafeProgram program) :
    RequestProgram AuthoritySafeRequest program :=
  publication_authority_program (Publication.publisher_safe source)

theorem image_authority_program (run : UInt64) (bundle : Validation.Bundle) (overlay : List Image.Entry) :
    RequestProgram AuthoritySafeRequest (Image.create run bundle overlay) := by
  unfold Image.create
  split
  · exact .pure _
  · apply request_bind (request_weaken
      (read_only_namespace_passive (Image.copyIdentified_readOnly _ _ _)) (fun _ => passive_authority_safe))
    intro copied
    cases copied with
    | error => exact .pure _
    | ok base =>
      apply RequestProgram.call (by intro setting; cases setting)
      intro reply
      dsimp only [Filesystem.Program.bind]
      split
      · exact .pure _
      · apply request_weaken (Image.contentClose_requests _ _ _)
        intro request source setting
        rcases source with writing | closing
        · rw [writing.1] at setting; cases setting
        · rw [closing] at setting; cases setting

theorem cleanup_authority_safe (run : RunDirectory.Owned) (input : Publication.Input)
    {before : List Program.Event} {request : Request} {observed : Option Reply}
    (source : Program.Prefix (cleanupRun run input)
      (before ++ [Program.filesystemPrefixEvent (request, observed)])) : AuthoritySafeRequest request := by
  have same : cleanupRun run input =
      if input.outcome.vmCleanup == "unknown" then Program.liftFilesystem (Validation.releaseDirectory run)
      else Program.liftFilesystem (RunDirectory.cleanup run) := rfl
  rw [same] at source
  split at source
  · exact passive_authority_safe (selected_filesystem_profile (validator_release_passive run) source)
  · exact selected_filesystem_profile (run_cleanup_authority_program run) source

theorem validator_authority_safe {bundle : Validation.Bundle} {raw : ByteArray}
    {before : List Program.Event} {request : Request} {observed : Option Reply}
    (source : ValidatorMutation bundle raw before (Program.filesystemPrefixEvent (request, observed))) :
    AuthoritySafeRequest request := by
  cases source with
  | allocating active => exact selected_filesystem_profile run_creation_authority_program active
  | writing context inside active trace =>
    exact selected_filesystem_profile (safe_authority_program (Publication.writeNew_safe _ _ _ _)) active
  | cleaningFailedWrite context writing error written inside active trace =>
    exact selected_filesystem_profile (run_cleanup_authority_program _) active
  | cleaningObserved context inside reaped active trace =>
    exact selected_filesystem_profile (run_cleanup_authority_program _) active
  | releasingUnknown context inside unknown active trace =>
    exact passive_authority_safe (selected_filesystem_profile (validator_release_passive _) active)

theorem run_authority_safe {request : GatewayWire.Request} {bundle : Validation.Bundle}
    {duration : Option Nat} {before : List Program.Event} {operation : Request} {observed : Option Reply}
    (source : RunMutation request bundle duration before (Program.filesystemPrefixEvent (operation, observed))) :
    AuthoritySafeRequest operation := by
  cases source with
  | preparing source =>
    cases source with
    | validating context inside source trace => exact validator_authority_safe source
    | revalidating context inside source trace => exact validator_authority_safe source
  | allocating context inside active trace => exact selected_filesystem_profile run_creation_authority_program active
  | imaging context inside active trace => exact selected_filesystem_profile (image_authority_program _ _ _) active
  | dispatching context inside active trace =>
    exact passive_authority_safe (dispatch_namespace_passive _ _ _ _ _ _ _ _ active)
  | cleaning context inside active trace => exact cleanup_authority_safe _ _ active
  | publishing context inside active trace =>
    exact selected_filesystem_profile (publication_authority_program (Publication.publish_prefix_program _ _ _)) active

-- §FS-host-boundary.ownership: Attribute names are derived from the actual packet/CLI caller.
theorem entrypoint_authority_safe {before : List Program.Event} {request : Request} {observed : Option Reply}
    (source : Program.Prefix Entrypoint.run (before ++ [Program.filesystemPrefixEvent (request, observed)])) :
    AuthoritySafeRequest request := by
  intro setting
  have mutating : ¬ NamespacePassive request := by
    intro passive
    unfold NamespacePassive at passive
    rw [setting] at passive
    exact passive
  obtain ⟨entry⟩ := entrypoint_mutation_origin source mutating
  have active := entry.source
  cases active with
  | validating context raw loading loaded inside active trace =>
    obtain ⟨role⟩ := validator_mutation_origin _ _ active
    exact validator_authority_safe role setting
  | executing context inside command active trace =>
    obtain ⟨role⟩ := run_mutation_origin _ _ _ active mutating
    exact run_authority_safe role setting

-- §FS-host-boundary.acceptance: The primitive's user-setting condition has a real producer.
theorem selected_authority_safe {kernel : Contract} {runtime : ActorRuntime kernel}
    {initial : World} {final : Population} {ticks : List (ActorTick runtime)}
    (journal : ActorJournal runtime (Population.empty initial) ticks final)
    {position : Nat} {tick : ActorTick runtime} {actor : ActorId} {engine : EngineState}
    {request : Request} {observed : Option Reply}
    (selected : ticks[position]? = some tick)
    (action : tick.action.eventFor actor = some (Program.filesystemPrefixEvent (request, observed)))
    (present : tick.before.actors actor = some engine) : AuthoritySafeRequest request :=
  entrypoint_authority_safe (selected_source_prefix journal selected action present)

theorem tracked_attribute_is_not_acl {name : ByteArray} (tracked : TrackedAttribute name) :
    name ≠ "system.posix_acl_access".toUTF8 ∧ name ≠ "system.posix_acl_default".toUTF8 := by
  rcases tracked with privateName | publicationName
  · rw [privateName]
    decide
  · rw [publicationName]
    decide

-- §FS-host-boundary.ownership: Caller-selected bytes cannot induce either POSIX ACL setter.
theorem actual_no_acl_setter {before : List Program.Event} {request : Request} {observed : Option Reply}
    (source : Program.Prefix Entrypoint.run (before ++ [Program.filesystemPrefixEvent (request, observed)]))
    (setting : request.op = .setAttribute) :
    request.left ≠ "system.posix_acl_access".toUTF8 ∧ request.left ≠ "system.posix_acl_default".toUTF8 :=
  tracked_attribute_is_not_acl (entrypoint_authority_safe source setting)

end LeanCage.Host.Kernel
