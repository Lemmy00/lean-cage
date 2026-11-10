import ArtifactsProofs.Manifest

namespace LeanCage.Host.Artifacts

open Filesystem

theorem componentParts_nonempty (input reversed : List Char) : componentParts input reversed ≠ [] := by
  induction input generalizing reversed with
  | nil => simp [componentParts]
  | cons scalar rest ih =>
    by_cases separator : scalar = '/'
    · subst scalar; simp [componentParts]
    · simpa only [componentParts, separator, ite_false] using ih (scalar :: reversed)

-- §FS-host-boundary.artifacts: Components used for materialization reconstruct the manifest path.
theorem componentParts_identity (input reversed : List Char) :
    ['/'].intercalate ((componentParts input reversed).map String.toList) = reversed.reverse ++ input := by
  induction input generalizing reversed with
  | nil => simp [componentParts]
  | cons scalar rest ih =>
    by_cases separator : scalar = '/'
    · subst scalar
      simp only [componentParts, List.map_cons, String.toList_ofList]
      rw [List.intercalate_cons_of_ne_nil (by simpa using componentParts_nonempty rest [])]
      simp only [ih, List.reverse_nil, List.nil_append, List.singleton_append, List.append_assoc]
    · simpa only [componentParts, separator, ite_false, List.reverse_cons, List.append_assoc,
        List.singleton_append] using ih (scalar :: reversed)

theorem pathComponents_identity (path : String) :
    String.ofList (['/'].intercalate ((pathComponents path).map String.toList)) = path := by
  simp only [pathComponents, componentParts_identity, List.reverse_nil, List.nil_append, String.ofList_toList]

theorem unhexLoop_size (input : List UInt8) (before after : ByteArray)
    (accepted : unhexLoop input before = .ok after) :
    input.length % 2 = 0 ∧ after.size = before.size + input.length / 2 := by
  cases input with
  | nil => cases accepted; simp
  | cons first tail =>
    cases tail with
    | nil => contradiction
    | cons second rest =>
      unfold unhexLoop at accepted
      split at accepted
      · have sizes := unhexLoop_size rest _ after accepted
        simp only [List.length_cons, ByteArray.size_push] at *
        omega
      · contradiction
termination_by input.length
decreasing_by simp_wf; simp_all only [List.length_cons]; omega

-- §FS-host-boundary.artifacts: Decoded paths retain the exact canonical manifest byte identity.
theorem decodePath_identity (encoded : ByteArray) (path : ExportPath)
    (accepted : decodePath encoded = .ok path) :
    encoded.size ≤ 8190 ∧ encoded.size % 2 = 0 ∧
      (Snapshot.hex path.text.toUTF8).toUTF8 = encoded := by
  unfold decodePath at accepted
  simp only [bind, Except.bind] at accepted
  split at accepted
  · contradiction
  · rename_i within
    obtain ⟨raw, _, continued⟩ := except_bind_ok accepted
    split at continued
    · contradiction
    · rename_i canonical
      cases decoded : String.fromUTF8? raw with
      | none => simp [decoded] at continued
      | some text =>
        simp only [decoded] at continued
        split at continued
        · contradiction
        · rename_i exactBytes
          split at continued
          · cases continued
            have upper : encoded.size ≤ 8190 := by
              apply Nat.not_lt.mp
              intro tooLarge
              exact within (by simp [tooLarge])
            have even : encoded.size % 2 = 0 := by
              apply Classical.byContradiction
              intro odd
              have different : (encoded.size % 2 != 0) = true := bne_iff_ne.mpr odd
              exact within (by simp only [different, Bool.or_true])
            have same : text.toUTF8 = raw := by simpa using exactBytes
            refine ⟨upper, even, ?_⟩
            rw [same]
            simpa using canonical
          · contradiction

-- §FS-host-boundary.artifacts: At most five field buffers are retained by the actual splitter.
theorem splitFields_count (fuel : Nat) (input : List UInt8) (current : ByteArray)
    (reversed fields : List ByteArray) (prior : reversed.length ≤ 4)
    (accepted : splitFields fuel input current reversed = .ok fields) : fields.length ≤ 5 := by
  induction fuel generalizing input current reversed fields with
  | zero => contradiction
  | succ fuel ih =>
    cases input with
    | nil =>
      cases accepted
      simpa only [List.length_reverse, List.length_cons] using Nat.add_le_add_right prior 1
    | cons byte rest =>
      unfold splitFields at accepted
      split at accepted
      · split at accepted
        · contradiction
        · have next : (current :: reversed).length ≤ 4 := by simp only [List.length_cons]; omega
          exact ih rest .empty _ fields next accepted
      · exact ih rest _ reversed fields prior accepted

end LeanCage.Host.Artifacts
