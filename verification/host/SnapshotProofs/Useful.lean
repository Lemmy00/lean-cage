import SnapshotProofs.Origins

namespace LeanCage.Host.Snapshot

open Filesystem

private def usefulInput : ByteArray := "x".toUTF8
private def usefulDigest : ByteArray := ⟨#[45, 113, 22, 66, 183, 38, 176, 68, 1, 98, 124, 169, 251, 172, 50, 245, 200, 83, 15, 177, 144, 60, 196, 219, 2, 37, 135, 23, 146, 26, 72, 129]⟩
private def usefulLimits : Limits := ⟨16, 8, 4⟩
private def usefulFrozen : Frozen := {
  tree := none
  stdin := some usefulInput
  treeDigest := none
  stdinDigest := some usefulDigest
  entries := #[]
  blobs := [⟨usefulDigest, usefulInput⟩]
  count := 2
  workspaceBytes := 0
}

-- §FS-host-boundary.snapshot: The actual producer has a useful successful stdin/hash execution.
theorem useful_stdin_run :
    Returns (freeze none (.bytes usefulInput) usefulLimits)
      [({ op := .sha256, left := usefulInput }, (0, usefulDigest))] (.ok usefulFrozen) := by
  apply Returns.call
  exact Returns.pure _

-- §FS-host-boundary.snapshot: A rejected bound returns before any primitive effect.
theorem unsupported_bound_run :
    ∃ error, Returns (freeze none .absent ⟨16, 1, 4⟩) [] (.error error) := by
  exact ⟨_, Returns.pure _⟩

end LeanCage.Host.Snapshot
