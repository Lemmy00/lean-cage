import SnapshotProofs.Format

namespace LeanCage.Host.Snapshot

private theorem ascii_nat (n : Nat) (bounded : n < 128) : (Char.ofNat n).toNat = n := by
  have valid : n.isValidChar := Or.inl (by omega)
  simp only [Char.ofNat, dite_eq_left valid, Char.ofNatAux, Char.toNat]
  exact UInt32.toNat_ofNatLT

-- §FS-workspace.filesystem: Distinct byte values cannot acquire the same lowercase hex spelling.
theorem hex_digit_unique {character : Char} {first second : Nat}
    (left : HexDigit character first) (right : HexDigit character second) : first = second := by
  rcases left with ⟨firstBounded, ⟨firstSmall, firstChar⟩ | ⟨firstLarge, firstChar⟩⟩ <;>
    rcases right with ⟨secondBounded, ⟨secondSmall, secondChar⟩ | ⟨secondLarge, secondChar⟩⟩ <;>
    have same := congrArg Char.toNat (firstChar.symm.trans secondChar) <;>
    rw [ascii_nat _ (by omega), ascii_nat _ (by omega)] at same <;> omega

theorem hex_meaning_unique {first second : List UInt8} {text : List Char}
    (left : HexMeaning first text) (right : HexMeaning second text) : first = second := by
  induction left generalizing second with
  | nil => cases right; rfl
  | byte value high low firstChar secondChar before after firstDigit secondDigit exactByte rest ih =>
    cases right with
    | byte other high' low' _ _ _ _ firstDigit' secondDigit' otherByte rest' =>
      have sameHigh := hex_digit_unique firstDigit firstDigit'
      have sameLow := hex_digit_unique secondDigit secondDigit'
      have sameByte : value = other := UInt8.toNat_inj.mp (by omega)
      rw [sameByte, ih rest']

theorem hex_injective {first second : ByteArray} (same : hex first = hex second) : first = second := by
  have text : (hex first).toList = (hex second).toList := congrArg String.toList same
  have values := hex_meaning_unique (hex_meaning first) (text ▸ hex_meaning second)
  exact ByteArray.ext (Array.toList_inj.mp values)

end LeanCage.Host.Snapshot
