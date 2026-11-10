import SnapshotProofs.Copy

namespace LeanCage.Host.Snapshot

def entriesBytes (entries : Array Entry) : Nat :=
  entries.foldl (fun total entry => total + entry.size) 0

def canonicalTree (entries : Array Entry) : ByteArray :=
  entries.foldl (fun bytes entry => bytes ++ entry.line) "LCTREE1\n".toUTF8

def entryNames (entries : Array Entry) : List String :=
  entries.toList.map (fun entry => entry.path.text)

-- §FS-host-boundary.snapshot: Exact format and aggregate counts are maintained together.
structure StateValid (limits : Limits) (state : State) : Prop where
  count_exact : state.count = 2 + state.entries.size
  bytes_exact : state.total = entriesBytes state.entries
  tree_exact : state.tree = canonicalTree state.entries
  inodes_bound : state.count ≤ limits.workspaceInodes
  bytes_bound : state.total ≤ limits.workspaceBytes
  tree_bound : state.tree.size ≤ treeMax
  unique : (entryNames state.entries).Nodup

theorem initial_state_valid (limits : Limits) (minimum : 2 ≤ limits.workspaceInodes) :
    StateValid limits {} := by
  refine ⟨rfl, rfl, rfl, minimum, Nat.zero_le _, ?_, by simp [entryNames]⟩
  decide

theorem appendEntry_preserves (limits : Limits) (state : State) (entry : Entry)
    (valid : StateValid limits state) {after : State}
    (accepted : appendEntry limits state entry = .ok after) : StateValid limits after := by
  unfold appendEntry at accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  · rename_i countBound
    split at accepted
    · cases accepted
    · rename_i bytesBound
      split at accepted
      · cases accepted
      · rename_i treeBound
        split at accepted
        · cases accepted
        · rename_i fresh
          cases accepted
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp only [Array.size_push]
            have exactCount := valid.count_exact
            omega
          · simp only [entriesBytes, Array.foldl_push]
            exact congrArg (fun total => total + entry.size) valid.bytes_exact
          · simp only [canonicalTree, Array.foldl_push]
            exact congrArg (fun tree => tree ++ entry.line) valid.tree_exact
          · change state.count + 1 ≤ limits.workspaceInodes
            omega
          · change state.total + entry.size ≤ limits.workspaceBytes
            omega
          · simpa only [ByteArray.size_append] using Nat.le_of_not_gt treeBound
          · have absent : entry.path.text ∉ entryNames state.entries := by
              intro present
              obtain ⟨earlier, member, equal⟩ := List.mem_map.mp present
              apply fresh
              apply Array.any_eq_true'.mpr
              exact ⟨earlier, by simpa using member, beq_iff_eq.mpr equal⟩
            simp only [entryNames, Array.toList_push, List.map_append, List.map_cons, List.map_nil]
            exact List.nodup_append.mpr ⟨valid.unique, by simp, by
              intro before member last singleton equal
              simp only [List.mem_singleton] at singleton
              cases singleton
              exact absent (equal ▸ member)⟩

theorem state_paths_valid (state : State) :
    ∀ entry ∈ state.entries.toList, ValidPath entry.path.text := by
  intro entry member
  exact entry.path.valid

end LeanCage.Host.Snapshot
