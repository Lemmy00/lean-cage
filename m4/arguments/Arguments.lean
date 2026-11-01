-- SPDX-License-Identifier: Apache-2.0
-- §AR-m4-controller.arguments: Live argument lengths and a strict computational interface.
import Bounds
namespace LeanCageM4.Arguments
open LeanCageM3 LeanCageM4.Plan LeanCageM4.Bounds

def lengthsValid : List Nat → Bool
  | [] => true
  | n :: rest => (!(n == 0) && n ≤ 4096) && lengthsValid rest

def nulBytes : List Nat → Nat
  | [] => 0
  | n :: rest => n + 1 + nulBytes rest

def nativeArgumentLengths (sizes : List Nat) : Bool × Nat :=
  (lengthsValid sizes, nulBytes sizes)

def guestSizes (argv : Array String) : List Nat := argv.toList.map String.utf8ByteSize

theorem lengthsValid_all (sizes : List Nat) :
    lengthsValid sizes = sizes.all (fun n => !(n == 0) && n ≤ 4096) := by
  induction sizes with
  | nil => rfl
  | cons n rest ih => simp only [lengthsValid, List.all_cons, ih]

theorem lengthsValid_exact (sizes : List Nat) :
    lengthsValid sizes = true ↔ ∀ n ∈ sizes, 1 ≤ n ∧ n ≤ 4096 := by
  rw [lengthsValid_all, List.all_eq_true]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h n mem
    have p := h n mem
    have nonzero : n ≠ 0 := by simpa using p.1
    exact ⟨by omega, p.2⟩
  · intro h n mem
    have p := h n mem
    exact ⟨by simpa using (show n ≠ 0 by omega), p.2⟩

theorem guestSizes_count (argv : Array String) : (guestSizes argv).length = argv.size := by
  simp only [guestSizes, List.length_map, Array.length_toList]

theorem guestSizes_utf8 (argv : Array String) :
    guestSizes argv = argv.toList.map (fun s => s.toUTF8.data.toList.length) := by
  simp only [guestSizes, Array.length_toList]
  rfl

theorem nulBytes_fold (sizes : List Nat) (initial : Nat) :
    sizes.foldl (fun total n => total + n + 1) initial = initial + nulBytes sizes := by
  induction sizes generalizing initial with
  | nil => simp [nulBytes]
  | cons n rest ih => simp only [List.foldl_cons, nulBytes, ih]; omega

theorem guestBytes_exact (p : Policy) : nulBytes (guestSizes p.argv) = guestBytes p := by
  simp only [guestSizes, guestBytes, ← Array.foldl_toList]
  simpa only [List.foldl_map, Nat.zero_add, Function.comp_def] using (nulBytes_fold (p.argv.toList.map String.utf8ByteSize) 0).symm

theorem valid_sizes (argv : Array String) (valid : argvValid argv = true) :
    lengthsValid (guestSizes argv) = true := by
  simp only [argvValid, Bool.and_eq_true] at valid
  have all := valid.1.2
  rw [← Array.all_toList, List.all_eq_true] at all
  rw [lengthsValid_all, guestSizes, List.all_map, List.all_eq_true]
  intro s mem
  have h := all s mem
  simp only [Bool.and_eq_true] at h
  simpa only [Function.comp_def, Bool.and_eq_true, String.isEmpty_eq_utf8ByteSize_beq_zero] using h.1

theorem valid_native_profile (p : Policy) (valid : argvValid p.argv = true) :
    nativeArgumentLengths (guestSizes p.argv) = (true, guestBytes p) := by
  simp only [nativeArgumentLengths, valid_sizes p.argv valid, guestBytes_exact]

theorem native_guest_suffix (executable : String) (p : Policy) (pid : Nat) (pre : Bool) :
    ((nativeArgs executable p pid pre).toList.drop 16).map String.utf8ByteSize = guestSizes p.argv := by
  rw [native_guest_arguments]
  rfl

end LeanCageM4.Arguments
