import PublicationProofs.Files
import PublicationProofs.Commit

namespace LeanCage.Host.Publication

open Filesystem

private theorem cleanup_footer (stage : Directories.Fresh) : SafeProgram (do
    for name in ["policy.json", "boot.log", "vm-report.json", "stdout", "stderr",
        "stored-report.json", "export.manifest", "result.json", "publication.wire"] do
      let _ ← Filesystem.Program.effect {op := .unlinkAt, first := stage.directory.fd, left := name.toUTF8}
    let _ ← Filesystem.Program.effect {
      op := .unlinkAt, first := stage.directory.fd, second := 512, left := "export".toUTF8 }
    let _ ← Filesystem.Program.effect {op := .close, first := stage.directory.fd}
    let _ ← Filesystem.Program.effect {
      op := .unlinkAt, first := stage.container.fd, second := 512, left := stage.name }
    let _ ← Filesystem.Program.effect {op := .close, first := stage.container.fd}
    pure ()) := by
  apply safe_bind
  · apply forIn_safe
    intro name state
    apply SafeProgram.call (by exact .inl rfl)
    intro reply
    exact .pure _
  · intro finished
    apply SafeProgram.call (by exact .inr rfl)
    intro reply
    apply SafeProgram.call (by trivial)
    intro reply
    apply SafeProgram.call (by exact .inr rfl)
    intro reply
    apply SafeProgram.call (by trivial)
    intro reply
    exact .pure _

theorem cleanup_safe (parent : Directories.Parent) (stage : Directories.Fresh) (input : Input) :
    SafeProgram (cleanup parent stage input) := by
  unfold cleanup
  apply safe_bind (readOnly_safe (Retrieval.openAt_readOnly _ _ _))
  intro opened
  dsimp only
  split
  · apply safe_bind
    · apply forIn_safe
      intro file state
      apply safe_bind (unlinkRelative_safe _ _ _ _)
      intro ignored
      exact .pure _
    · intro finished
      apply safe_bind
      · apply forIn_safe
        intro path state
        apply safe_bind (unlinkRelative_safe _ _ _ _)
        intro ignored
        exact .pure _
      · intro finished
        apply SafeProgram.call (by trivial)
        intro reply
        exact cleanup_footer _
  · exact cleanup_footer _

theorem closeOwned_safe (parent : Directories.Parent) (stage : Directories.Fresh) :
    SafeProgram (closeOwned parent stage) := by
  unfold closeOwned
  apply SafeProgram.call (by trivial)
  intro reply
  apply SafeProgram.call (by trivial)
  intro reply
  apply SafeProgram.call (by trivial)
  intro reply
  exact .pure _

theorem authenticate_sized (bundle : Validation.Bundle) (wire : ByteArray) :
    Snapshot.PostProgram (fun result => match result with
      | .error _ => True | .ok tag => tag.size = 32) (authenticate bundle wire) := by
  apply Snapshot.post_of_returns
  intro events result run
  cases result with
  | error => trivial
  | ok tag =>
    obtain ⟨_, _, _, _, _, _, _, _, sized⟩ := Retrieval.authenticate_source _ _ run
    exact sized

theorem prepare_safe (bundle : Validation.Bundle) (input : Input) (target : ByteArray)
    (stdoutHash stderrHash : ByteArray) (parent : Directories.Parent) (stage : Directories.Fresh) :
    SafeProgram (prepare bundle input target stdoutHash stderrHash parent stage) := by
  unfold prepare
  apply safe_bind (readOnly_safe (Retrieval.readOnly_snapshot (Snapshot.hash_input _)))
  intro policyDigest
  cases policyDigest with
  | error => exact .pure _
  | ok policyDigest =>
    dsimp only
    split
    · split
      · exact .pure _
      · apply safe_bind_post (readOnly_safe (Retrieval.authenticate_readOnly _ _)) (authenticate_sized _ _)
        intro digest sized
        cases digest with
        | error => exact .pure _
        | ok digest =>
          dsimp only
          apply safe_bind (fill_safe _ _ _ _ _)
          intro filled
          cases filled with
          | error => exact .pure _
          | ok filled =>
            apply SafeProgram.call
            · exact ⟨rfl, by simp only [marker, ByteArray.size_append, sized]; rfl⟩
            · intro reply
              dsimp only [Filesystem.Program.bind]
              split <;> exact .pure _
    · exact .pure _

-- §FS-host-boundary.publication: Only the explicit commit site may request rename.
def PublisherRequest (request : Request) : Prop := request.op = .renameNew ∨ SafeRequest request

inductive PublisherProgram {α : Type} : Filesystem.Program α → Prop where
  | pure (value : α) : PublisherProgram (.pure value)
  | call {request : Request} {next : Reply → Filesystem.Program α}
      (allowed : PublisherRequest request) (tail : ∀ reply, PublisherProgram (next reply)) :
      PublisherProgram (.call request next)

theorem publisher_bind {α β : Type} {program : Filesystem.Program α} {next : α → Filesystem.Program β}
    (first : PublisherProgram program) (tail : ∀ value, PublisherProgram (next value)) :
    PublisherProgram (program.bind next) := by
  induction first with
  | pure => exact tail _
  | call allowed rest ih => exact .call allowed ih

theorem publisher_safe {α : Type} {program : Filesystem.Program α} (safe : SafeProgram program) :
    PublisherProgram program := by
  induction safe with
  | pure => exact .pure _
  | call allowed rest ih => exact .call (.inr allowed) ih

theorem attempt_prefix (bundle : Validation.Bundle) (input : Input) (target : ByteArray)
    (stdoutHash stderrHash : ByteArray) : PublisherProgram (attempt bundle input target stdoutHash stderrHash) := by
  unfold attempt
  apply publisher_bind (publisher_safe (readOnly_safe (Retrieval.absolute_readOnly _)))
  intro display
  cases display with
  | error => exact .pure _
  | ok display =>
    apply publisher_bind (publisher_safe (parent_safe _ _))
    intro parent
    cases parent with
    | error => exact .pure _
    | ok parent =>
      apply publisher_bind (publisher_safe (fresh_safe _))
      intro fresh
      cases fresh with
      | error => exact publisher_safe (readOnly_safe (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _)))
      | ok stage =>
        apply publisher_bind (publisher_safe (prepare_safe _ _ _ _ _ _ _))
        intro prepared
        cases prepared with
        | error =>
          apply publisher_bind (publisher_safe (cleanup_safe _ _ _))
          intro ignored
          exact publisher_safe (readOnly_safe (Retrieval.readOnly_snapshot (Snapshot.closeResult_input _ _)))
        | ok outcome =>
          apply PublisherProgram.call (by exact .inl rfl)
          intro renamed
          dsimp only [Filesystem.Program.bind]
          unfold finishCommit
          apply publisher_bind (publisher_safe (closeOwned_safe _ _))
          intro ignored
          split
          · exact .pure _
          · split
            · exact .pure _
            · exact .pure _

theorem publish_prefix_program (request : GatewayWire.Request) (bundle : Validation.Bundle) (input : Input) :
    PublisherProgram (publish request bundle input) := by
  unfold publish
  apply publisher_bind (publisher_safe (readOnly_safe (Retrieval.identify_readOnly _)))
  intro identified
  cases identified with
  | error =>
    apply publisher_bind (publisher_safe (readOnly_safe (Retrieval.publicationDestination_readOnly _ _ _)))
    intro target
    cases target with
    | error => exact .pure _
    | ok target => exact publisher_bind (attempt_prefix _ _ _ _ _) (fun _ => .pure _)
  | ok hashes =>
    cases hashes
    apply publisher_bind (publisher_safe (readOnly_safe (Retrieval.publicationDestination_readOnly _ _ _)))
    intro target
    cases target with
    | error => exact .pure _
    | ok target => exact publisher_bind (attempt_prefix _ _ _ _ _) (fun _ => .pure _)

theorem publisher_prefix {α : Type} {program : Filesystem.Program α}
    {events : List (Request × Option Reply)} (verified : PublisherProgram program)
    (run : Prefix program events) : ∀ event ∈ events, PublisherRequest event.1 := by
  induction run with
  | empty => simp
  | lost request next => cases verified with | call allowed => simpa using allowed
  | returned request next reply events run ih =>
    cases verified with
    | call allowed tail =>
      intro event member
      rcases List.mem_cons.mp member with rfl | member
      · exact allowed
      · exact ih (tail reply) event member

-- §FS-host-boundary.publication: A lost final call keeps exclusive opens and bounded writes.
theorem publish_request_prefix (request : GatewayWire.Request) (bundle : Validation.Bundle) (input : Input)
    {events : List (Request × Option Reply)} (run : Prefix (publish request bundle input) events) :
    ∀ event ∈ events, PublisherRequest event.1 := publisher_prefix (publish_prefix_program _ _ _) run

end LeanCage.Host.Publication
