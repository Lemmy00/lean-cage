-- SPDX-License-Identifier: Apache-2.0
-- §AR-m4-controller.plan: Candidate parent argument bytes; integration review remains open.
import Plan
namespace LeanCageM4.Parent
open LeanCageM3 LeanCageM4.Plan

theorem native_parent_decoded (executable : String) (p : Policy) (pid : UInt32) (pre : Bool) :
    ((nativeArgs executable p pid.toNat pre)[12]?).bind
      (fun s => parseDecimal 18446744073709551615 (s.toUTF8.data.toList.map UInt8.toNat)) = some pid.toNat := by
  rw [native_parent]
  exact actual_decimal_accepted _ _ (parent_uint32_fits pid)

theorem native_parent_byte_shape (executable : String) (p : Policy) (pid : UInt32) (pre : Bool)
    (s : String) (entry : (nativeArgs executable p pid.toNat pre)[12]? = some s) :
    s.toUTF8.data.toList ≠ [] ∧ (0 : UInt8) ∉ s.toUTF8.data.toList ∧ s.toUTF8.size ≤ 20 := by
  rw [native_parent] at entry
  cases entry
  exact ⟨actual_decimal_nonempty _, actual_decimal_no_nul _, actual_decimal_size _ (parent_uint32_fits pid)⟩
end LeanCageM4.Parent
