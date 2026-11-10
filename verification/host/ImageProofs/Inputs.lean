import ImageProofs.Source
import Std.Data.TreeSet.Lemmas

namespace LeanCage.Host.Image
open Filesystem

def EntryOrigin (request bundle : String) (preflight : Bool) (fault : Nat)
    (policy : Policy.Accepted) (frozen : Snapshot.Frozen) (entry : Entry) : Prop :=
  entry ∈ [⟨"request", 16832, .empty⟩, ⟨"m3-inputs/trees", 16832, .empty⟩,
    ⟨"m3-inputs/blobs", 16832, .empty⟩, ⟨"request/policy.json", 33024, policy.raw⟩,
    ⟨"request/config", 33024, requestConfig request bundle preflight policy.transport fault⟩] ∨
  (∃ tree digest, frozen.tree = some tree ∧ frozen.treeDigest = some digest ∧
    entry = ⟨"m3-inputs/trees/" ++ Snapshot.hex digest, 33024, tree⟩) ∨
  ∃ blob ∈ frozen.blobs, entry = ⟨"m3-inputs/blobs/" ++ Snapshot.hex blob.digest, 33024, blob.bytes⟩

-- §FS-host-boundary.snapshot: Overlay entries come only from bound fields and actual frozen blobs.
theorem entries_source (request bundle : String) (preflight : Bool) (fault : Nat)
    (policy : Policy.Accepted) (frozen : Snapshot.Frozen) :
    ∀ entry ∈ entries request bundle preflight fault policy frozen,
      EntryOrigin request bundle preflight fault policy frozen entry := by
  intro entry member
  unfold entries at member
  rcases List.mem_append.mp member with before | blobs
  · rcases List.mem_append.mp before with fixed | tree
    · exact .inl fixed
    · cases selectedTree : frozen.tree with
      | none => simp only [selectedTree] at tree; cases tree
      | some data =>
        cases selectedDigest : frozen.treeDigest with
        | none => simp only [selectedTree, selectedDigest] at tree; cases tree
        | some digest =>
          simp only [selectedTree, selectedDigest, List.mem_singleton] at tree
          exact .inr (.inl ⟨data, digest, selectedTree, selectedDigest, tree⟩)
  · obtain ⟨blob, present, same⟩ := List.mem_map.mp blobs
    exact .inr (.inr ⟨blob, List.mem_mergeSort.mp present, same.symm⟩)

theorem entry_valid_fields (entry : Entry) (valid : entry.valid = true) :
    Validation.canonicalName entry.name = true ∧ entry.name.toUTF8.size ≤ 4095 ∧
    entry.bytes.size ≤ workspaceMax ∧ (entry.mode = 16832 ∨ entry.mode = 33024) := by
  simpa only [Entry.valid, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc] using valid

def overlayBytes (overlay : List Entry) : Nat := overlay.foldl (fun total entry => total + entry.bytes.size) 0

-- §FS-host-boundary.snapshot: The actual guard bounds counts, names, modes and archive data.
theorem overlay_bounds (overlay : List Entry) (accepted : overlayValid overlay = true) :
    overlay.length ≤ inodeMax + 8 ∧
    (∀ entry ∈ overlay, Validation.canonicalName entry.name = true ∧ entry.name.toUTF8.size ≤ 4095 ∧
      entry.bytes.size ≤ workspaceMax ∧ (entry.mode = 16832 ∨ entry.mode = 33024)) ∧
    overlayBytes overlay ≤ workspaceMax + stdinMax + treeMax + reportMax + 256 := by
  unfold overlayValid at accepted
  have fields : overlay.length ≤ inodeMax + 8 ∧ overlay.all Entry.valid = true ∧
      overlayBytes overlay ≤ workspaceMax + stdinMax + treeMax + reportMax + 256 ∧
      (overlay.foldl (fun (state : Bool × Std.TreeSet String compare) entry =>
        (state.1 && !state.2.contains entry.name, state.2.insert entry.name)) (true, ∅)).1 = true := by
    simpa only [Bool.and_eq_true, decide_eq_true_eq, and_assoc, overlayBytes] using accepted
  exact ⟨fields.1, fun entry member => entry_valid_fields entry (List.all_eq_true.mp fields.2.1 entry member),
    fields.2.2.1⟩

-- §FS-host-boundary.snapshot: Numeric header fields fit the actual newc32-bit representation.
theorem overlay_header_fields (overlay : List Entry) (accepted : overlayValid overlay = true) :
    overlay.length + 2 < 2 ^ 32 ∧ ∀ entry ∈ overlay,
      entry.mode < 2 ^ 32 ∧ entry.bytes.size < 2 ^ 32 ∧ entry.name.toUTF8.size + 1 < 2 ^ 32 := by
  have fields := overlay_bounds overlay accepted
  constructor
  · have count := fields.1
    change overlay.length ≤ 65544 at count
    omega
  · intro entry member
    have value := fields.2.1 entry member
    have bytes : entry.bytes.size ≤ 268435456 := value.2.2.1
    rcases value.2.2.2 with mode | mode <;> omega

theorem pad4_bound (count : Nat) : (pad4 count).size ≤ 3 ∧ (count + (pad4 count).size) % 4 = 0 := by
  simp only [pad4, zeros, ByteArray.size, Array.size_replicate]
  omega

end LeanCage.Host.Image

namespace LeanCage.Host.Image
open Filesystem

private theorem overlay_names_aux (overlay : List Entry) (flag : Bool) (seen : Std.TreeSet String compare)
    (accepted : (overlay.foldl (fun (state : Bool × Std.TreeSet String compare) entry =>
      (state.1 && !state.2.contains entry.name, state.2.insert entry.name)) (flag, seen)).1 = true) :
    flag = true ∧ (overlay.map Entry.name).Nodup ∧ ∀ entry ∈ overlay, seen.contains entry.name = false := by
  induction overlay generalizing flag seen with
  | nil => exact ⟨accepted, by simp, by simp⟩
  | cons entry rest ih =>
    have next := ih _ _ accepted
    have checked : flag = true ∧ seen.contains entry.name = false := by
      simpa [Bool.and_eq_true] using next.1
    refine ⟨checked.1, List.nodup_cons.mpr ⟨?_, next.2.1⟩, ?_⟩
    · intro present
      obtain ⟨other, member, same⟩ := List.mem_map.mp present
      have absent := next.2.2 other member
      simp [Std.TreeSet.contains_insert, same] at absent
    · intro other member
      rcases List.mem_cons.mp member with rfl | member
      · exact checked.2
      · have absent := next.2.2 other member
        rw [Std.TreeSet.contains_insert] at absent
        cases first : compare entry.name other.name == .eq <;> simp_all

-- §FS-host-boundary.snapshot: The actual checked overlay cannot repeat an archive path.
theorem overlay_unique (overlay : List Entry) (accepted : overlayValid overlay = true) :
    (overlay.map Entry.name).Nodup := by
  unfold overlayValid at accepted
  have fields := accepted
  simp only [Bool.and_eq_true] at fields
  exact (overlay_names_aux overlay true ∅ fields.2).2.1

end LeanCage.Host.Image
