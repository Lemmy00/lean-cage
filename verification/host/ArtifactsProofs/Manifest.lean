import ArtifactsProofs.Report
import Std.Data.TreeMap.Lemmas

namespace LeanCage.Host.Artifacts

open Filesystem

def nodeBytes (nodes : List Node) : Nat := (nodes.map Node.size).sum

def nodeOmitted (nodes : List Node) : Nat :=
  (nodes.map (fun node => if node.kind = .omitted then 1 else 0)).sum

structure ManifestInvariant (limits : Transport.Limits) (state : ManifestState) : Prop where
  count : state.entries.size ≤ limits.inodesMax
  total : state.total ≤ limits.workspaceMax
  bytes : nodeBytes state.entries.toList = state.total
  omitted : nodeOmitted state.entries.toList = state.omitted
  indexSound : ∀ key kind, state.kinds[key]? = some kind →
    ∃ node ∈ state.entries.toList, node.path.text = key ∧ node.kind = kind
  indexComplete : ∀ node ∈ state.entries.toList, state.kinds[node.path.text]? = some node.kind
  unique : state.entries.toList.Pairwise (fun first second => first.path.text ≠ second.path.text)

theorem manifest_initial (limits : Transport.Limits) : ManifestInvariant limits {} := by
  refine ⟨Nat.zero_le _, Nat.zero_le _, rfl, rfl, ?_, ?_, ?_⟩
  · intro key kind lookup
    simp at lookup
  · simp
  · simp

theorem appendNode_fields (limits : Transport.Limits) (before after : ManifestState) (node : Node)
    (accepted : appendNode limits before node = .ok after) :
    before.entries.size + 1 ≤ limits.inodesMax ∧ before.total + node.size ≤ limits.workspaceMax ∧
    before.kinds.contains node.path.text = false ∧
    after = {
      entries := before.entries.push node
      kinds := before.kinds.insert node.path.text node.kind
      total := before.total + node.size
      omitted := before.omitted + (if node.kind = .omitted then 1 else 0) } := by
  unfold appendNode at accepted
  split at accepted
  · contradiction
  · split at accepted
    · contradiction
    · split at accepted
      · contradiction
      · rename_i absent
        cases accepted
        exact ⟨by omega, by omega, Bool.eq_false_iff.mpr absent, rfl⟩

theorem manifest_append (limits : Transport.Limits) (before after : ManifestState) (node : Node)
    (invariant : ManifestInvariant limits before) (accepted : appendNode limits before node = .ok after) :
    ManifestInvariant limits after := by
  rcases appendNode_fields limits before after node accepted with ⟨count, total, absent, rfl⟩
  have distinct : ∀ old ∈ before.entries.toList, old.path.text ≠ node.path.text := by
    intro old member equal
    have lookup := invariant.indexComplete old member
    rw [Std.TreeMap.contains_eq_isSome_getElem?, ← equal, lookup] at absent
    contradiction
  refine ⟨by simpa only [Array.size_push] using count, total, ?_, ?_, ?_, ?_, ?_⟩
  · change nodeBytes (before.entries.push node).toList = before.total + node.size
    rw [Array.toList_push]
    simp only [nodeBytes, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    exact congrArg (· + node.size) invariant.bytes
  · change nodeOmitted (before.entries.push node).toList =
      before.omitted + (if node.kind = .omitted then 1 else 0)
    rw [Array.toList_push]
    simp only [nodeOmitted, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    exact congrArg (· + (if node.kind = .omitted then 1 else 0)) invariant.omitted
  · intro key kind lookup
    change (before.kinds.insert node.path.text node.kind)[key]? = some kind at lookup
    rw [Std.TreeMap.getElem?_insert] at lookup
    split at lookup
    · rename_i same
      have equal : node.path.text = key := by simpa using same
      cases lookup
      exact ⟨node, by simp, equal, rfl⟩
    · rcases invariant.indexSound key kind lookup with ⟨old, member, key, kind⟩
      exact ⟨old, by simp [member], key, kind⟩
  · intro old member
    change old ∈ (before.entries.push node).toList at member
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at member
    change (before.kinds.insert node.path.text node.kind)[old.path.text]? = some old.kind
    rw [Std.TreeMap.getElem?_insert]
    rcases member with previous | rfl
    · have different := distinct old previous
      have notCompare : compare node.path.text old.path.text ≠ .eq := by
        intro same
        have keys : node.path.text = old.path.text := by simpa using same
        exact different keys.symm
      simp only [notCompare, ite_false]
      exact invariant.indexComplete old previous
    · simp
  · change (before.entries.push node).toList.Pairwise _
    rw [Array.toList_push]
    apply List.pairwise_append.mpr
    refine ⟨invariant.unique, by simp, ?_⟩
    intro old member new last
    have equal : new = node := by simpa using last
    subst new
    exact distinct old member

-- §FS-host-boundary.artifacts: Every retained node was counted before the next line is read.
theorem scanManifest_invariant (fuel : Nat) (limits : Transport.Limits) (raw : ByteArray)
    (offset : Nat) (current : ByteArray) (before after : ManifestState)
    (invariant : ManifestInvariant limits before)
    (accepted : scanManifest fuel limits raw offset current before = .ok after) :
    ManifestInvariant limits after := by
  induction fuel generalizing offset current before after with
  | zero => contradiction
  | succ fuel ih =>
    unfold scanManifest at accepted
    split at accepted
    · dsimp only at accepted
      split at accepted
      · split at accepted
        · contradiction
        · obtain ⟨node, _, remaining⟩ := except_bind_ok accepted
          obtain ⟨next, appended, continued⟩ := except_bind_ok remaining
          exact ih _ _ next after (manifest_append limits before next node invariant appended) continued
      · split at accepted
        · contradiction
        · exact ih _ _ before after invariant accepted
    · split at accepted
      · cases accepted
        exact invariant
      · contradiction

theorem parseManifest_sound (limits : Transport.Limits) (raw : ByteArray) (state : ManifestState)
    (accepted : parseManifest limits raw = .ok state) :
    raw.size ≤ manifestMax ∧ ManifestInvariant limits state ∧ hierarchy state = true := by
  unfold parseManifest at accepted
  simp only [bind, Except.bind] at accepted
  split at accepted
  · contradiction
  · rename_i format
    cases scanned : scanManifest (raw.size + 1) limits raw 10 .empty {} with
    | error error => simp [scanned] at accepted
    | ok result =>
      rw [scanned] at accepted
      dsimp only at accepted
      split at accepted
      · contradiction
      · rename_i good
        cases accepted
        have bound : ¬ raw.size > manifestMax := by
          intro tooLarge
          exact format (by simp [tooLarge])
        exact ⟨Nat.not_lt.mp bound,
          scanManifest_invariant _ _ _ _ _ _ _ (manifest_initial limits) scanned,
          by simpa using good⟩

-- §FS-host-boundary.artifacts: Every proper parent names a real declared directory.
theorem manifest_hierarchy (limits : Transport.Limits) (state : ManifestState)
    (invariant : ManifestInvariant limits state) (checked : hierarchy state = true) :
    ∀ node ∈ state.entries.toList, ∀ parent ∈ node.path.parents,
      ∃ directory ∈ state.dirs, directory.text = parent := by
  intro node member parent parentMember
  have declared := List.all_eq_true.mp (List.all_eq_true.mp checked node member) parent parentMember
  have lookup : state.kinds[parent]? = some .directory := of_decide_eq_true declared
  rcases invariant.indexSound parent .directory lookup with ⟨found, foundMember, same, kind⟩
  cases found with
  | directory path =>
    exact ⟨path, List.mem_filterMap.mpr ⟨.directory path, foundMember, rfl⟩, same⟩
  | file => contradiction
  | omitted => contradiction

end LeanCage.Host.Artifacts
