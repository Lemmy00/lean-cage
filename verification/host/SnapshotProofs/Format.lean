import SnapshotProofs.Enumeration

namespace LeanCage.Host.Snapshot

-- §FS-workspace.filesystem: Lowercase hex has two independently interpreted digits per byte.
def HexDigit (character : Char) (value : Nat) : Prop :=
  value < 16 ∧ ((value < 10 ∧ character = Char.ofNat (48 + value)) ∨
    (10 ≤ value ∧ character = Char.ofNat (87 + value)))

inductive HexMeaning : List UInt8 → List Char → Prop where
  | nil : HexMeaning [] []
  | byte (value : UInt8) (high low : Nat) (first second : Char)
      (before : List UInt8) (after : List Char)
      (firstDigit : HexDigit first high) (secondDigit : HexDigit second low)
      (exactByte : value.toNat = 16 * high + low) (rest : HexMeaning before after) :
      HexMeaning (value :: before) (first :: second :: after)

private theorem hex_digit (value : Nat) (bounded : value < 16) :
    HexDigit (hexChar value) value := by
  unfold hexChar HexDigit
  split
  · exact ⟨bounded, .inl ⟨by assumption, rfl⟩⟩
  · exact ⟨bounded, .inr ⟨by omega, rfl⟩⟩

theorem hex_meaning (bytes : ByteArray) : HexMeaning bytes.data.toList (hex bytes).toList := by
  unfold hex
  rw [String.toList_ofList]
  generalize bytes.data.toList = values
  induction values with
  | nil => exact .nil
  | cons byte rest ih =>
    have bounded := byte.toNat_lt
    apply HexMeaning.byte byte (byte.toNat / 16) (byte.toNat % 16)
      (hexChar (byte.toNat / 16)) (hexChar (byte.toNat % 16)) rest _
    · apply hex_digit
      omega
    · exact hex_digit _ (by omega)
    · omega
    · exact ih

theorem hex_length (bytes : ByteArray) : (hex bytes).toList.length = 2 * bytes.size := by
  have meaning := hex_meaning bytes
  have length : ∀ {values text}, HexMeaning values text → text.length = 2 * values.length := by
    intro values text observed
    induction observed with
    | nil => rfl
    | byte => simp_all only [List.length_cons]; omega
  simpa only [Array.length_toList, ByteArray.size] using length meaning

theorem bytesLE_total (first second : List UInt8) :
    bytesLE first second = true ∨ bytesLE second first = true := by
  induction first generalizing second with
  | nil => exact .inl rfl
  | cons a rest ih =>
    cases second with
    | nil => exact .inr rfl
    | cons b more =>
      by_cases same : a = b
      · subst b
        simpa [bytesLE] using ih more
      · have different : a.toNat ≠ b.toNat := fun equal => same (UInt8.toNat_inj.mp equal)
        simp only [bytesLE, ite_eq_right same, ite_eq_right (Ne.symm same), decide_eq_true_eq]
        omega

theorem bytesLE_trans (first second third : List UInt8)
    (left : bytesLE first second = true) (right : bytesLE second third = true) :
    bytesLE first third = true := by
  induction first generalizing second third with
  | nil => rfl
  | cons a rest ih =>
    cases second with
    | nil => cases left
    | cons b more =>
      cases third with
      | nil => cases right
      | cons c tail =>
        by_cases ab : a = b
        · subst b
          by_cases ac : a = c
          · subst c
            simp only [bytesLE, ↓reduceIte] at left right ⊢
            exact ih more tail left right
          · simpa only [bytesLE, ite_eq_right ac] using right
        · by_cases bc : b = c
          · subst c
            simpa only [bytesLE, ite_eq_right ab] using left
          · have abLess : a.toNat < b.toNat := by
              simpa only [bytesLE, ite_eq_right ab, decide_eq_true_eq] using left
            have bcLess : b.toNat < c.toNat := by
              simpa only [bytesLE, ite_eq_right bc, decide_eq_true_eq] using right
            have ac : a ≠ c := by
              intro equal
              subst c
              omega
            simp only [bytesLE, ite_eq_right ac, decide_eq_true_eq]
            omega

-- §FS-host-boundary.snapshot: Sorting uses unsigned UTF-8 byte order on the bounded name list.
theorem sortNames_sorted (names : List String) :
    (sortNames names).Pairwise (fun a b => bytesLE a.toUTF8.data.toList b.toUTF8.data.toList = true) := by
  exact List.pairwise_mergeSort
    (fun a b c => bytesLE_trans a.toUTF8.data.toList b.toUTF8.data.toList c.toUTF8.data.toList)
    (fun a b => by simpa only [Bool.or_eq_true] using bytesLE_total a.toUTF8.data.toList b.toUTF8.data.toList) names

end LeanCage.Host.Snapshot
