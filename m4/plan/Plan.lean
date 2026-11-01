-- SPDX-License-Identifier: Apache-2.0
import Decimal

-- §AR-m4-controller.plan: Exact argument positions and bounded numeric fields.
namespace LeanCageM4.Plan
open LeanCageM3

def numericFields (l : Limits) : List Nat :=
  [l.memory, l.tasks, l.quota, l.cpu, l.wall, l.workspace, l.inodes,
   l.stdin, l.stdout, l.stderr]

theorem plan_size (p : Policy) (pid : Nat) (pre : Bool) :
    (planArgs p pid pre).size = 15 + p.argv.size := by
  simp [planArgs]

theorem plan_mode (p : Policy) (pid : Nat) (pre : Bool) :
    (planArgs p pid pre)[0]? = some (if pre then "M3CHECK1" else "M3PLAN1") := by
  simp [planArgs, Array.getElem?_append]

theorem plan_parent (p : Policy) (pid : Nat) (pre : Bool) :
    (planArgs p pid pre)[11]? = some (toString pid) := by
  simp [planArgs, Array.getElem?_append]

theorem plan_numeric_fields (p : Policy) (pid : Nat) (pre : Bool) :
    ((planArgs p pid pre).toList.drop 1).take 10 =
      (numericFields p.limits).map toString := by
  simp [planArgs, numericFields]

theorem plan_argv (p : Policy) (pid : Nat) (pre : Bool) :
    (planArgs p pid pre).toList.drop 15 = p.argv.toList := by
  simp [planArgs]

theorem decimal_roundtrip (n : Nat) : (toString n).toNat? = some n := by
  simp

theorem limits_numeric_width (l : Limits) (valid : limitsValid l = true) :
    ∀ n ∈ numericFields l, n ≤ 18446744073709551615 := by
  simp only [limitsValid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at valid
  intro n hn
  simp only [numericFields, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega


theorem plan_export (p : Policy) (pid : Nat) (pre : Bool) :
    (planArgs p pid pre)[12]? = some (if p.exportFiles then "regular-files" else "discard") := by
  simp [planArgs, Array.getElem?_append]

theorem plan_workspace_digest (p : Policy) (pid : Nat) (pre : Bool) :
    (planArgs p pid pre)[13]? = some ((p.workspaceInput.map (fun s => (s.drop 7).toString)).getD "none") := by
  simp [planArgs, Array.getElem?_append]

theorem plan_stdin_digest (p : Policy) (pid : Nat) (pre : Bool) :
    (planArgs p pid pre)[14]? = some ((p.stdinInput.map (fun s => (s.drop 7).toString)).getD "none") := by
  simp [planArgs, Array.getElem?_append]

theorem numeric_fields_decoded (p : Policy) (pid : Nat) (pre : Bool)
    (valid : limitsValid p.limits = true) :
    (((planArgs p pid pre).toList.drop 1).take 10).map
      (fun s => parseDecimal 18446744073709551615 (s.toUTF8.data.toList.map UInt8.toNat)) =
      (numericFields p.limits).map some := by
  rw [plan_numeric_fields, List.map_map]
  apply List.map_congr_left
  intro n hn
  exact actual_decimal_accepted _ n (limits_numeric_width p.limits valid n hn)

theorem parent_field_decoded (p : Policy) (pid : Nat) (pre : Bool)
    (within : pid ≤ 18446744073709551615) :
    ((planArgs p pid pre)[11]?).bind
      (fun s => parseDecimal 18446744073709551615 (s.toUTF8.data.toList.map UInt8.toNat)) = some pid := by
  rw [plan_parent]
  exact actual_decimal_accepted _ pid within

theorem valid_period (l : Limits) (valid : limitsValid l = true) : l.period = 100000 := by
  simp only [limitsValid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at valid
  omega

-- §AR-m4-controller.plan: This pure prepend exposes the runtime representation obligation.
def nativeArgs (executable : String) (p : Policy) (pid : Nat) (pre : Bool) : Array String :=
  #[executable] ++ planArgs p pid pre

theorem native_argument_count (executable : String) (p : Policy) (pid : Nat) (pre : Bool) :
    (nativeArgs executable p pid pre).size = 16 + p.argv.size := by
  simp only [nativeArgs, Array.size_append, Array.size_singleton, plan_size]
  omega

theorem native_executable (executable : String) (p : Policy) (pid : Nat) (pre : Bool) :
    (nativeArgs executable p pid pre)[0]? = some executable := by
  simp [nativeArgs, Array.getElem?_append]

theorem native_mode (executable : String) (p : Policy) (pid : Nat) (pre : Bool) :
    (nativeArgs executable p pid pre)[1]? = some (if pre then "M3CHECK1" else "M3PLAN1") := by
  simpa [nativeArgs, Array.getElem?_append] using plan_mode p pid pre

theorem native_numeric_fields (executable : String) (p : Policy) (pid : Nat) (pre : Bool) :
    ((nativeArgs executable p pid pre).toList.drop 2).take 10 =
      (numericFields p.limits).map toString := by
  simpa [nativeArgs] using plan_numeric_fields p pid pre

theorem native_parent (executable : String) (p : Policy) (pid : Nat) (pre : Bool) :
    (nativeArgs executable p pid pre)[12]? = some (toString pid) := by
  simpa [nativeArgs, Array.getElem?_append] using plan_parent p pid pre

theorem native_export (executable : String) (p : Policy) (pid : Nat) (pre : Bool) :
    (nativeArgs executable p pid pre)[13]? = some (if p.exportFiles then "regular-files" else "discard") := by
  simpa [nativeArgs, Array.getElem?_append] using plan_export p pid pre

theorem native_digests (executable : String) (p : Policy) (pid : Nat) (pre : Bool) :
    (nativeArgs executable p pid pre)[14]? = some ((p.workspaceInput.map (fun s => (s.drop 7).toString)).getD "none") ∧
    (nativeArgs executable p pid pre)[15]? = some ((p.stdinInput.map (fun s => (s.drop 7).toString)).getD "none") := by
  constructor
  · simpa [nativeArgs, Array.getElem?_append] using plan_workspace_digest p pid pre
  · simpa [nativeArgs, Array.getElem?_append] using plan_stdin_digest p pid pre

theorem native_guest_arguments (executable : String) (p : Policy) (pid : Nat) (pre : Bool) :
    (nativeArgs executable p pid pre).toList.drop 16 = p.argv.toList := by
  simpa [nativeArgs] using plan_argv p pid pre

theorem native_count_valid (executable : String) (p : Policy) (pid : Nat) (pre : Bool)
    (valid : argvValid p.argv = true) :
    17 ≤ (nativeArgs executable p pid pre).size ∧ (nativeArgs executable p pid pre).size ≤ 80 := by
  rw [native_argument_count]
  simp only [argvValid, Bool.and_eq_true, decide_eq_true_eq] at valid
  omega


theorem numeric_fields_byte_shape (p : Policy) (pid : Nat) (pre : Bool)
    (valid : limitsValid p.limits = true) (s : String)
    (member : s ∈ ((planArgs p pid pre).toList.drop 1).take 10) :
    s.toUTF8.data.toList ≠ [] ∧ (0 : UInt8) ∉ s.toUTF8.data.toList ∧ s.toUTF8.size ≤ 20 := by
  rw [plan_numeric_fields] at member
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp member
  exact ⟨actual_decimal_nonempty n, actual_decimal_no_nul n,
    actual_decimal_size n (limits_numeric_width p.limits valid n hn)⟩

theorem parent_uint32_fits (pid : UInt32) : pid.toNat ≤ 18446744073709551615 := by
  have bound := pid.toNat_lt
  omega

theorem parent_uint32_decoded (p : Policy) (pid : UInt32) (pre : Bool) :
    ((planArgs p pid.toNat pre)[11]?).bind
      (fun s => parseDecimal 18446744073709551615 (s.toUTF8.data.toList.map UInt8.toNat)) = some pid.toNat :=
  parent_field_decoded p pid.toNat pre (parent_uint32_fits pid)

def sampleLimits : Limits :=
  ⟨16777216, 4, 1000, 100000, 10000, 10, 1048576, 64, 0, 0, 0⟩
def samplePolicy : Policy :=
  ⟨#["/bin/sh", "-c", "true"], none, none, false, sampleLimits⟩

theorem allowed_plan_example :
    limitsValid samplePolicy.limits = true ∧ argvValid samplePolicy.argv = true ∧
    (nativeArgs "/leancage-m3-helper" samplePolicy 42 false).toList =
      ["/leancage-m3-helper", "M3PLAN1", "16777216", "4", "1000", "10000", "10",
       "1048576", "64", "0", "0", "0", "42", "discard", "none", "none", "/bin/sh", "-c", "true"] := by
  simp only [argvValid, ← Array.all_toList, ← Array.foldl_toList, String.contains_char_eq]
  decide

theorem preflight_plan_example :
    (nativeArgs "/leancage-m3-helper" {samplePolicy with exportFiles := true} 42 true).toList =
      ["/leancage-m3-helper", "M3CHECK1", "16777216", "4", "1000", "10000", "10",
       "1048576", "64", "0", "0", "0", "42", "regular-files", "none", "none", "/bin/sh", "-c", "true"] := by decide

theorem rejected_policy_examples :
    limitsValid {sampleLimits with memory := 0} = false ∧
    limitsValid {sampleLimits with period := 1} = false ∧
    argvValid #[] = false ∧ argvValid #["/bin/unknown"] = false ∧
    argvValid #["/bin/sh", "bad\x00arg"] = false := by
  simp only [argvValid, ← Array.all_toList, ← Array.foldl_toList, String.contains_char_eq]
  decide

end LeanCageM4.Plan
