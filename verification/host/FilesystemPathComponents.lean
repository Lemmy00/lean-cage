import FilesystemPublicationHandles
import Init.Data.List.SplitOn.Lemmas

namespace LeanCage.Host.Kernel
open Filesystem

private theorem split_chars (bytes accumulated : List UInt8)
    (nonzero : ∀ byte ∈ bytes, byte ≠ 0)
    (prefixChars : ∀ byte ∈ accumulated, byte ≠ 0 ∧ byte ≠ 47) :
    ∀ part ∈ List.splitOnPPrepend (fun byte => byte == 47) bytes accumulated,
      ∀ byte ∈ part, byte ≠ 0 ∧ byte ≠ 47 := by
  induction bytes generalizing accumulated with
  | nil =>
    intro part member byte occurs
    have same : part = accumulated.reverse := by simpa only [List.splitOnPPrepend_nil, List.mem_singleton] using member
    apply prefixChars byte
    simpa only [same, List.mem_reverse] using occurs
  | cons head tail ih =>
    intro part member
    rw [List.splitOnPPrepend_cons_eq_ite] at member
    split at member
    · rcases List.mem_cons.mp member with rfl | following
      · intro byte occurs
        exact prefixChars byte (by simpa only [List.mem_reverse] using occurs)
      · exact ih [] (fun byte occurs => nonzero byte (by simp [occurs])) (by simp) part following
    · rename_i separator
      apply ih (head :: accumulated) (fun byte occurs => nonzero byte (by simp [occurs])) _ part member
      intro byte occurs
      rcases List.mem_cons.mp occurs with rfl | previous
      · exact ⟨nonzero byte (by simp), by simpa only [beq_iff_eq] using separator⟩
      · exact prefixChars byte previous

-- §FS-host-boundary.ownership: The actual byte splitter supplies complete single-component
-- semantics, not only the later size/private-prefix check.
theorem source_components_complete (path : ByteArray) (parts : List ByteArray)
    (accepted : SourcePaths.components path = .ok parts) :
    ∀ part ∈ parts, Directories.component part = true ∧ PrivateNames.reservedBytes part = false := by
  obtain ⟨empty, valid, shape, bounded⟩ := Snapshot.sourceComponents_fields path parts accepted
  have rawFields : path.size ≤ 4095 ∧ (0 : UInt8) ∉ path.data.toList := by simpa [rawPathValid] using valid
  have noZero := rawFields.2
  intro name member
  have bound := bounded name member
  rw [shape] at member
  obtain ⟨part, filtered, same⟩ := List.mem_map.mp member
  subst name
  have actual := List.mem_filter.mp filtered
  have nonempty : part ≠ [] := by
    intro same
    rw [same] at actual
    cases actual.2
  have chars : ∀ byte ∈ part, byte ≠ 0 ∧ byte ≠ 47 := by
    apply split_chars path.data.toList [] (fun byte occurs same => noZero (same ▸ occurs)) (by simp) part
    simpa only [List.splitOn_eq_splitOnP, List.splitOnP_eq_splitOnPPrepend] using actual.1
  have noZeroPart : (0 : UInt8) ∉ part := fun occurs => (chars 0 occurs).1 rfl
  have noSlashPart : (47 : UInt8) ∉ part := fun occurs => (chars 47 occurs).2 rfl
  refine ⟨?_, bound.2⟩
  simpa [Directories.component, ByteArray.isEmpty, ByteArray.size, nonempty,
    noZeroPart, noSlashPart, Array.contains_eq_mem] using bound.1

theorem selected_parent_component (path : ByteArray) (create : Bool)
    {events : List (Request × Reply)} {parent : Directories.Parent}
    (source : Returns (Directories.parent path create) events (.ok parent)) :
    Directories.component parent.name = true ∧ PrivateNames.reservedBytes parent.name = false := by
  obtain ⟨selected, identity, base, selecting, inspecting, descending, trace, started, named,
    notDot, notUp, success, empty, bounded, uid, inspected, descended⟩ := Retrieval.parent_source path create source
  have parsed : SourcePaths.components path = .ok selected.parts := by cases started <;> assumption
  exact source_components_complete path selected.parts parsed parent.name (List.mem_of_getLast? named)

theorem selected_fresh_component (parent : Directories.Parent) {events : List (Request × Reply)} {stage : Directories.Fresh}
    (source : Returns (Directories.fresh parent) events (.ok stage)) :
    Directories.component stage.name = true ∧ PrivateNames.reservedBytes stage.name = true := by
  obtain ⟨opening, creating, trace, opened, created⟩ := Publication.fresh_source parent source
  obtain ⟨random, randomEvents, made, later, shape, randomness, size, name, component,
    acknowledged, empty, childOpened, owner, mode⟩ := created
  refine ⟨component, ?_⟩
  rw [name]
  exact private_prefix_reserved _

end LeanCage.Host.Kernel
