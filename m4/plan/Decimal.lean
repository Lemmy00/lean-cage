-- SPDX-License-Identifier: Apache-2.0
import LeanCageM3.API
import Init.Data.Nat.ToString
import Init.Data.String.Lemmas
import Std.Data.String.ToNat

-- §AR-m4-controller.plan: Exact decimal bytes of the live Lean plan encoder.
namespace LeanCageM4.Plan

def decimalBytes (n : Nat) : List Nat := (Nat.toDigits 10 n).map Char.toNat

theorem decimalBytes_exact (n : Nat) :
    decimalBytes n = (Nat.toDigits 10 n).map Char.toNat := rfl

theorem decimal_bytes_digits (n b : Nat) (member : b ∈ decimalBytes n) :
    48 ≤ b ∧ b ≤ 57 := by
  rw [decimalBytes_exact] at member
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp member
  have digit := Nat.isDigit_of_mem_toDigits (by decide : 0 < 10) (by decide : 10 ≤ 10) hc
  exact Char.isDigit_iff_toNat.mp digit

theorem decimal_bytes_nonempty (n : Nat) : decimalBytes n ≠ [] := by
  simp [decimalBytes_exact]

theorem ascii_utf8 (chars : List Char) (ascii : ∀ c ∈ chars, c.toNat < 128) :
    (String.ofList chars).toUTF8.data.toList.map UInt8.toNat = chars.map Char.toNat := by
  induction chars with
  | nil => rfl
  | cons c cs ih =>
    have hc := ascii c (by simp)
    have rest : ∀ d ∈ cs, d.toNat < 128 := by intro d hd; exact ascii d (by simp [hd])
    have size : c.utf8Size = 1 := by simp [Char.utf8Size, UInt32.le_iff_toNat_le, show c.toNat ≤ 127 by omega]
    rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList,
      List.utf8Encode_cons, List.utf8Encode_singleton, String.utf8EncodeChar_eq_singleton size]
    simp only [ByteArray.toList_data_append, List.data_toByteArray, List.toList_toArray,
      List.map_cons, List.cons_append, List.nil_append]
    rw [UInt32.toNat_toUInt8]
    change c.toNat % 256 :: _ = c.toNat :: _
    rw [Nat.mod_eq_of_lt (by omega : c.toNat < 256)]
    exact congrArg (List.cons c.toNat) (ih rest)

theorem decimal_utf8 (n : Nat) :
    (toString n).toUTF8.data.toList.map UInt8.toNat = decimalBytes n := by
  rw [Nat.toString_eq_repr, Nat.repr_eq_ofList_toDigits]
  rw [ascii_utf8, decimalBytes_exact]
  intro c hc
  have digit := Char.isDigit_iff_toNat.mp (Nat.isDigit_of_mem_toDigits (by decide : 0 < 10) (by decide : 10 ≤ 10) hc)
  change 48 ≤ c.toNat ∧ c.toNat ≤ 57 at digit
  omega


def decimalFold : Nat → List Nat → Nat
  | acc, [] => acc
  | acc, b :: bytes => decimalFold (acc * 10 + (b - 48)) bytes

def decimalDigits : List Nat → Bool
  | [] => true
  | b :: bytes => (48 ≤ b && b ≤ 57) && decimalDigits bytes

def parseDecimal (bound : Nat) (bytes : List Nat) : Option Nat :=
  match bytes with
  | [] => none
  | _ :: _ =>
    if decimalDigits bytes && decimalFold 0 bytes ≤ bound
    then some (decimalFold 0 bytes) else none

theorem decimal_digits_exact (bytes : List Nat) :
    decimalDigits bytes = true ↔ ∀ b ∈ bytes, 48 ≤ b ∧ b ≤ 57 := by
  induction bytes with
  | nil => simp [decimalDigits]
  | cons b bs ih => simp [decimalDigits, ih, and_assoc]

theorem decimal_fold_chars (chars : List Char) (acc : Nat) :
    decimalFold acc (chars.map Char.toNat) = Nat.ofDigitChars 10 chars acc := by
  induction chars generalizing acc with
  | nil => rfl
  | cons c cs ih =>
    change decimalFold (acc * 10 + (c.toNat - 48)) (cs.map Char.toNat) =
      Nat.ofDigitChars 10 cs (10 * acc + (c.toNat - 48))
    rw [Nat.mul_comm 10 acc]
    exact ih (acc * 10 + (c.toNat - 48))

theorem decimal_fold_value (n : Nat) : decimalFold 0 (decimalBytes n) = n := by
  rw [decimalBytes_exact, decimal_fold_chars, Nat.ofDigitChars_ten_toDigits]

theorem parse_decimal_exact (bound : Nat) (bytes : List Nat) (n : Nat) :
    parseDecimal bound bytes = some n ↔
      bytes ≠ [] ∧ (∀ b ∈ bytes, 48 ≤ b ∧ b ≤ 57) ∧
      decimalFold 0 bytes = n ∧ n ≤ bound := by
  cases bytes with
  | nil => simp [parseDecimal]
  | cons b bs =>
    simp only [parseDecimal, Bool.and_eq_true, decide_eq_true_eq, decimal_digits_exact]
    split
    · rename_i good
      constructor
      · intro eq
        have value := Option.some.inj eq
        exact ⟨List.cons_ne_nil _ _, good.1, value, value ▸ good.2⟩
      · intro h
        exact congrArg some h.2.2.1
    · rename_i bad
      constructor
      · intro impossible
        cases impossible
      · intro h
        exact False.elim (bad ⟨h.2.1, h.2.2.1 ▸ h.2.2.2⟩)

theorem actual_decimal_accepted (bound n : Nat) (within : n ≤ bound) :
    parseDecimal bound ((toString n).toUTF8.data.toList.map UInt8.toNat) = some n := by
  rw [decimal_utf8, parse_decimal_exact]
  exact ⟨decimal_bytes_nonempty n, decimal_bytes_digits n, decimal_fold_value n, within⟩

theorem actual_decimal_overflow (bound n : Nat) (over : bound < n) :
    parseDecimal bound ((toString n).toUTF8.data.toList.map UInt8.toNat) = none := by
  rw [decimal_utf8]
  cases bytes_eq : decimalBytes n with
  | nil => exact False.elim (decimal_bytes_nonempty n bytes_eq)
  | cons b bs =>
    have value : decimalFold 0 (b :: bs) = n := bytes_eq ▸ decimal_fold_value n
    simp [parseDecimal, value, show ¬ n ≤ bound by omega]


theorem actual_decimal_digits (n : Nat) (b : UInt8)
    (member : b ∈ (toString n).toUTF8.data.toList) : 48 ≤ b.toNat ∧ b.toNat ≤ 57 := by
  apply decimal_bytes_digits n b.toNat
  rw [← decimal_utf8]
  exact List.mem_map.mpr ⟨b, member, rfl⟩

theorem actual_decimal_no_nul (n : Nat) :
    (0 : UInt8) ∉ (toString n).toUTF8.data.toList := by
  intro member
  have impossible := actual_decimal_digits n 0 member
  simp at impossible

theorem actual_decimal_nonempty (n : Nat) : (toString n).toUTF8.data.toList ≠ [] := by
  intro empty
  have nonempty := decimal_bytes_nonempty n
  rw [← decimal_utf8, empty] at nonempty
  exact nonempty rfl

theorem decimal_bytes_length (n : Nat) (within : n ≤ 18446744073709551615) :
    (decimalBytes n).length ≤ 20 := by
  rw [decimalBytes_exact, List.length_map]
  apply (Nat.length_toDigits_le_iff (by decide : 1 < 10) (by decide : 0 < 20)).mpr
  omega

theorem actual_decimal_size (n : Nat) (within : n ≤ 18446744073709551615) :
    (toString n).toUTF8.size ≤ 20 := by
  have equal := congrArg List.length (decimal_utf8 n)
  simp only [List.length_map, Array.length_toList] at equal
  change (toString n).toUTF8.data.size ≤ 20
  rw [equal]
  exact decimal_bytes_length n within

theorem decimal_accepted_examples :
    parseDecimal 18446744073709551615 [48] = some 0 ∧
    parseDecimal 18446744073709551615 [48,48,52,50] = some 42 ∧
    parseDecimal 18446744073709551615 [52,50,57,52,57,54,55,50,57,54] = some 4294967296 ∧
    parseDecimal 18446744073709551615 [49,56,52,52,54,55,52,52,48,55,51,55,48,57,53,53,49,54,49,53] =
      some 18446744073709551615 := by decide

theorem decimal_rejected_examples :
    parseDecimal 18446744073709551615 [] = none ∧
    parseDecimal 18446744073709551615 [45,49] = none ∧
    parseDecimal 18446744073709551615 [43,49] = none ∧
    parseDecimal 18446744073709551615 [32,49] = none ∧
    parseDecimal 18446744073709551615 [49,0] = none ∧
    parseDecimal 18446744073709551615 [49,255] = none ∧
    parseDecimal 18446744073709551615 [49,56,52,52,54,55,52,52,48,55,51,55,48,57,53,53,49,54,49,54] = none := by decide

end LeanCageM4.Plan
