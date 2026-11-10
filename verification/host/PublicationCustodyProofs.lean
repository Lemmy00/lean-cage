import PublicationProofs
import RunDirectoryProofs.Requests

namespace LeanCage.Host.Publication
open Filesystem

def ReleaseRequest (parent : Directories.Parent) (stage : Directories.Fresh) (request : Request) : Prop :=
  request.op = .close ∧
    (request.first = stage.directory.fd ∨ request.first = stage.container.fd ∨
      request.first = parent.directory.fd)

theorem closeOwned_requests (parent : Directories.Parent) (stage : Directories.Fresh) :
    RequestProgram (ReleaseRequest parent stage) (closeOwned parent stage) := by
  unfold closeOwned
  apply RequestProgram.call ⟨rfl, .inl rfl⟩
  intro reply
  apply RequestProgram.call ⟨rfl, .inr (.inl rfl)⟩
  intro reply
  apply RequestProgram.call ⟨rfl, .inr (.inr rfl)⟩
  intro reply
  exact .pure _

theorem finishCommit_requests (parent : Directories.Parent) (stage : Directories.Fresh)
    (outcome : Outcome) (reply : Reply) :
    RequestProgram (ReleaseRequest parent stage) (finishCommit parent stage outcome reply) := by
  unfold finishCommit
  apply request_bind (closeOwned_requests _ _)
  intro ignored
  split
  · exact .pure _
  · split <;> exact .pure _

-- §FS-host-boundary.publication: Actual post-attempt error/loss prefixes only close owned FDs.
theorem finishCommit_release_prefix (parent : Directories.Parent) (stage : Directories.Fresh)
    (outcome : Outcome) (reply : Reply) {events : List (Request × Option Reply)}
    (source : Prefix (finishCommit parent stage outcome reply) events) :
    ∀ event ∈ events, ReleaseRequest parent stage event.1 :=
  request_prefix (finishCommit_requests _ _ _ _) source

-- §FS-host-boundary.publication: Native errors remain represented after the three actual closes.
theorem native_error_release_exists (parent : Directories.Parent) (stage : Directories.Fresh)
    (outcome : Outcome) :
    Returns (finishCommit parent stage outcome (0 - 5, .empty))
      [({ op := .close, first := stage.directory.fd }, (0, .empty)),
       ({ op := .close, first := stage.container.fd }, (0, .empty)),
       ({ op := .close, first := parent.directory.fd }, (0, .empty))]
      (.error (failure "atomic publication" (0 - 5, .empty))) := by
  apply Returns.call
  apply Returns.call
  apply Returns.call
  exact .pure _

-- §FS-host-boundary.publication: Losing the rename has no source continuation or rollback.
theorem lost_rename_prefix (parent : Directories.Parent) (stage : Directories.Fresh)
    (outcome : Outcome) :
    Prefix (.call {
      op := .renameNew
      first := stage.container.fd
      second := parent.directory.fd
      left := stage.name
      right := parent.name } (finishCommit parent stage outcome))
      [({
        op := .renameNew
        first := stage.container.fd
        second := parent.directory.fd
        left := stage.name
        right := parent.name }, none)] :=
  .lost _ _

end LeanCage.Host.Publication
