-- SPDX-License-Identifier: Apache-2.0
-- §AR-m4-controller.initialization: Flag bytes agree with the live native plan.
import Validation
namespace LeanCageM4.Initialization
open LeanCageM3 LeanCageM4.Plan LeanCageM4.Validation

theorem live_preflight_flag (executable : String) (p : Policy) (pid : Nat) (pre : Bool) :
    ((nativeArgs executable p pid pre)[1]?).map
      (fun s => bytesEq (utf8 s) checkBytes) = some pre := by
  rw [native_mode]
  cases pre <;> decide

theorem live_export_flag (executable : String) (p : Policy) (pid : Nat) (pre : Bool) :
    ((nativeArgs executable p pid pre)[13]?).map
      (fun s => bytesEq (utf8 s) filesBytes) = some p.exportFiles := by
  rw [native_export]
  cases p.exportFiles <;> decide

end LeanCageM4.Initialization
