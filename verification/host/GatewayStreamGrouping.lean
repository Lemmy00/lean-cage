import GatewayWriterCommitOrder

namespace LeanCage.Host.PrivateStreams

private theorem partition_at_first (chunks : List (Nat × Bytes)) (base : Nat)
    (ordered : chunks.Pairwise (fun first last => first.1 ≤ last.1))
    (bounded : ∀ item ∈ chunks, base ≤ item.1) :
    chunks = chunks.filter (fun item => item.1 == base) ++ chunks.filter (fun item => item.1 != base) := by
  induction chunks with
  | nil => rfl
  | cons head tail ih =>
    have pair := List.pairwise_cons.mp ordered
    by_cases same : head.1 = base
    · simp only [List.filter_cons, same, beq_self_eq_true, ite_true, bne_self_eq_false, Bool.false_eq_true, ite_false]
      simpa only [List.cons_append] using congrArg (List.cons head)
        (ih pair.2 (fun item member => bounded item (by simp [member])))
    · have positive : base < head.1 := by have lower := bounded head (by simp); omega
      have none : ∀ item ∈ tail, item.1 ≠ base := by
        intro item member equal
        have next := pair.1 item member
        omega
      have empty : tail.filter (fun item => item.1 == base) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro item member
        simp only [beq_iff_eq]
        exact none item member
      have all : tail.filter (fun item => item.1 != base) = tail := by
        apply List.filter_eq_self.mpr
        intro item member
        simpa only [bne_iff_ne] using none item member
      simp [same, empty, all]

-- §FS-host-boundary.caller: Source-ordered partial chunks can be grouped by
-- their actual call ordinal without changing byte order or repeating bytes.
theorem ordered_chunks_grouped (chunks : List (Nat × Bytes)) (base count : Nat)
    (ordered : chunks.Pairwise (fun first last => first.1 ≤ last.1))
    (bounded : ∀ item ∈ chunks, base ≤ item.1 ∧ item.1 < base + count) :
    chunks.flatMap Prod.snd = (List.range' base count).flatMap (fun ordinal =>
      (chunks.filter (fun item => item.1 == ordinal)).flatMap Prod.snd) := by
  induction count generalizing base chunks with
  | zero =>
    have empty : chunks = [] := by
      cases chunks with
      | nil => rfl
      | cons head tail => have bound := bounded head (by simp); omega
    simp only [empty, List.flatMap_nil, List.range'_zero]
  | succ count ih =>
    have partition := partition_at_first chunks base ordered (fun item member => (bounded item member).1)
    let tail := chunks.filter (fun item => item.1 != base)
    have tailOrdered : tail.Pairwise (fun first last => first.1 ≤ last.1) := ordered.filter _
    have tailBound : ∀ item ∈ tail, base + 1 ≤ item.1 ∧ item.1 < base + 1 + count := by
      intro item member
      obtain ⟨member, different⟩ := List.mem_filter.mp member
      have bound := bounded item member
      have different : item.1 ≠ base := by simpa only [bne_iff_ne] using different
      omega
    have grouped := ih tail (base + 1) tailOrdered tailBound
    have sameFilter : ∀ ordinal ∈ List.range' (base + 1) count,
        tail.filter (fun item => item.1 == ordinal) = chunks.filter (fun item => item.1 == ordinal) := by
      intro ordinal member
      have lower : base + 1 ≤ ordinal := by
        obtain ⟨index, inside, value⟩ := List.mem_range'.mp member
        omega
      change (chunks.filter (fun item => item.1 != base)).filter (fun item => item.1 == ordinal) = _
      rw [List.filter_filter]
      apply List.filter_congr
      intro item inside
      by_cases same : item.1 = ordinal
      · have different : ordinal ≠ base := by omega
        simp [same, different]
      · simp [same]
    rw [List.range'_succ, List.flatMap_cons]
    calc
      chunks.flatMap Prod.snd = (chunks.filter (fun item => item.1 == base)).flatMap Prod.snd ++ tail.flatMap Prod.snd := by
        simpa only [tail, List.flatMap_append] using congrArg (List.flatMap Prod.snd) partition
      _ = (chunks.filter (fun item => item.1 == base)).flatMap Prod.snd ++
          (List.range' (base + 1) count).flatMap (fun ordinal => (chunks.filter (fun item => item.1 == ordinal)).flatMap Prod.snd) := by
        rw [grouped]
        congr 1
        apply congrArg List.flatten
        apply List.map_congr_left
        intro ordinal member
        rw [sameFilter ordinal member]

end LeanCage.Host.PrivateStreams
