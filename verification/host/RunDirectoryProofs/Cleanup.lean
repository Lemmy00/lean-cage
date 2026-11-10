import RunDirectoryProofs.Requests

namespace LeanCage.Host.RunDirectory
open Filesystem

def CleanupRequest (owned : Owned) (request : Request) : Prop :=
  match request.op with
  | .unlinkAt =>
    (request.first = owned.directory.fd ∧ request.second = 0 ∧
      request.left ∈ ["request.cpio".toUTF8, "control.sock".toUTF8, "policy.json".toUTF8]) ∨
    (request.first = owned.container.fd ∧ request.second = 512 ∧ request.left = owned.name)
  | .close => request.first = owned.directory.fd ∨ request.first = owned.container.fd
  | _ => False

-- §FS-host-boundary.ownership: Cleanup names only retained own children and the created run name.
theorem cleanup_requests (owned : Owned) : RequestProgram (CleanupRequest owned) (cleanup owned) := by
  unfold cleanup
  apply request_bind
  · apply request_forIn
    intro name member state
    apply RequestProgram.call
    · refine .inl ⟨rfl, rfl, ?_⟩
      simpa using List.mem_map.mpr ⟨name, member, rfl⟩
    · intro reply
      exact .pure _
  · intro finished
    apply RequestProgram.call (by exact .inl rfl)
    intro reply
    apply RequestProgram.call (by exact .inr ⟨rfl, rfl, rfl⟩)
    intro reply
    apply RequestProgram.call (by exact .inr rfl)
    intro reply
    exact .pure _

theorem cleanup_request_prefix (owned : Owned) {events : List (Request × Option Reply)}
    (run : Prefix (cleanup owned) events) : ∀ event ∈ events, CleanupRequest owned event.1 :=
  request_prefix (cleanup_requests owned) run

end LeanCage.Host.RunDirectory
