import SnapshotProofs.Origins

namespace LeanCage.Host.Snapshot

open Filesystem

-- §FS-host-boundary.snapshot: Every new path is built solely from checked nonprivate components.
theorem acquired_public_paths {limits : Limits} {before after : State} {events : List (Request × Reply)}
    (observed : Acquired limits before events after) :
    ∀ entry ∈ after.entries.toList, entry ∈ before.entries.toList ∨ PublicPath entry.path.text := by
  induction observed with
  | unchanged => exact fun _ member => .inl member
  | sequence initial final first last =>
    intro entry member
    rcases last entry member with middle | publicPath
    · exact first entry middle
    · exact .inr publicPath
  | directory parent child prefixName name component notPrivate path pathValue pathPublic opened
      information stat descriptorValue statValue directory appended =>
    have entries := (appendEntry_update _ _ _ appended).1
    intro entry member
    simp only [entries, Array.toList_push, List.mem_append, List.mem_singleton] at member
    rcases member with old | same
    · exact .inl old
    · cases same
      exact .inr pathPublic
  | file parent child prefixName name component notPrivate path pathValue pathPublic opened
      information stat descriptorValue statValue regular linked copied reads closed digest copyValue bounded
      closeValue closeBytes digestSize blobs blobValue appended =>
    have entries := (appendEntry_update _ _ _ appended).1
    intro entry member
    simp only [entries, Array.toList_push, List.mem_append, List.mem_singleton] at member
    rcases member with old | same
    · exact .inl old
    · cases same
      exact .inr pathPublic

theorem freeze_public_paths (workspace : Option ByteArray) (stdin : Stdin) (limits : Limits)
    {events : List (Request × Reply)} {frozen : Frozen}
    (run : Returns (freeze workspace stdin limits) events (.ok frozen)) :
    ∀ entry ∈ frozen.entries.toList, PublicPath entry.path.text := by
  obtain ⟨_, state, workspaceEvents, _, _, _, _, workspaceRun, _, _, _, _, _, entries, _, _⟩ :=
    freeze_witness _ _ _ run
  intro entry member
  rw [entries] at member
  rcases acquired_public_paths (copyWorkspace_acquired _ _ workspaceRun) entry member with impossible | path
  · cases impossible
  · exact path

end LeanCage.Host.Snapshot
