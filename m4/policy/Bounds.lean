-- SPDX-License-Identifier: Apache-2.0
import Plan

-- §AR-m4-controller.bounds: Exact numeric predicate and live Lean policy validation.
namespace LeanCageM4.Bounds
open LeanCageM3 LeanCageM4.Plan

def pageRemainder : Nat → Nat → Nat
  | 0, n => n
  | fuel + 1, n => if (4096 ≤ n : Bool) then pageRemainder fuel (n - 4096) else n

theorem pageRemainder_exact (fuel n : Nat) (enough : n ≤ fuel) :
    pageRemainder fuel n = n % 4096 := by
  induction fuel generalizing n with
  | zero =>
    have zero : n = 0 := by omega
    subst n
    rfl
  | succ fuel ih =>
    simp only [pageRemainder]
    split
    · rename_i large
      have bound : 4096 ≤ n := of_decide_eq_true large
      rw [ih (n - 4096) (by omega), ← Nat.mod_eq_sub_mod bound]
    · rename_i small
      have bound : n < 4096 := by
        have notlarge : ¬4096 ≤ n := fun large => small (decide_eq_true large)
        omega
      exact (Nat.mod_eq_of_lt bound).symm

def pageAligned (n : Nat) : Bool := pageRemainder n n == 0

theorem pageAligned_exact (n : Nat) : pageAligned n = (n % 4096 == 0) := by
  simp only [pageAligned, pageRemainder_exact n n (Nat.le_refl n)]

def fieldAt : List Nat → Nat → Nat
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, i + 1 => fieldAt xs i

def fieldCount : List Nat → Nat
  | [] => 0
  | _ :: xs => fieldCount xs + 1

def nativeLimits (fields : List Nat) : Bool :=
  let memory := fieldAt fields 0
  let tasks := fieldAt fields 1
  let quota := fieldAt fields 2
  let cpu := fieldAt fields 3
  let wall := fieldAt fields 4
  let workspace := fieldAt fields 5
  let inodes := fieldAt fields 6
  let stdin := fieldAt fields 7
  let stdout := fieldAt fields 8
  let stderr := fieldAt fields 9
  fieldCount fields == 10 &&
  (16777216 ≤ memory && memory ≤ 1073741824 && pageAligned memory) &&
  (4 ≤ tasks && tasks ≤ 256) && (1000 ≤ quota && quota ≤ 100000) &&
  (10000 ≤ cpu && cpu ≤ 3600000000) && (10 ≤ wall && wall ≤ 3600000) &&
  (1048576 ≤ workspace && workspace ≤ 268435456 && pageAligned workspace) &&
  (64 ≤ inodes && inodes ≤ 65536) && stdin ≤ 67108864 &&
  stdout ≤ 16777216 && stderr ≤ 16777216

def nativeArguments (argc bytes : Nat) : Bool := argc - 16 ≤ 64 && bytes ≤ 16384

def nativeBounds (argc bytes : Nat) (fields : List Nat) : Bool :=
  nativeArguments argc bytes && nativeLimits fields

theorem limits_exact (l : Limits) :
    limitsValid l = (nativeLimits (numericFields l) && (l.period == 100000)) := by
  simp only [limitsValid, nativeLimits, numericFields, fieldAt, fieldCount, Nat.reduceAdd, Nat.reduceBEq, Bool.true_and, pageAligned_exact]
  cases h : l.period == 100000 <;>
    simp only [Bool.and_false, Bool.and_true, Bool.false_and, Bool.and_assoc]

theorem limits_accepted (l : Limits) (valid : limitsValid l = true) :
    nativeLimits (numericFields l) = true := by
  rw [limits_exact, Bool.and_eq_true] at valid
  exact valid.1

theorem limits_recovered (l : Limits) (period : l.period = 100000)
    (accepted : nativeLimits (numericFields l) = true) : limitsValid l = true := by
  simp only [limits_exact, accepted, period, BEq.rfl, Bool.and_self]

def guestBytes (p : Policy) : Nat :=
  p.argv.foldl (fun n s => n + s.utf8ByteSize + 1) 0

theorem argument_conditions (executable : String) (p : Policy) (pid : Nat) (pre : Bool)
    (valid : argvValid p.argv = true) :
    nativeArguments (nativeArgs executable p pid pre).size (guestBytes p) = true := by
  rw [native_argument_count]
  simp only [argvValid, Bool.and_eq_true, decide_eq_true_eq] at valid
  simp only [nativeArguments, guestBytes, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · omega
  · exact decide_eq_true valid.2

theorem valid_plan_bounds (executable : String) (p : Policy) (pid : Nat) (pre : Bool)
    (limits : limitsValid p.limits = true) (args : argvValid p.argv = true) :
    nativeBounds (nativeArgs executable p pid pre).size (guestBytes p)
      (numericFields p.limits) = true := by
  simp only [nativeBounds, argument_conditions executable p pid pre args,
    limits_accepted p.limits limits, Bool.and_self]

theorem allowed_boundary : nativeBounds 17 8 (numericFields sampleLimits) = true := by
  have valid : limitsValid sampleLimits = true := by decide
  simp only [nativeBounds, nativeArguments, limits_accepted sampleLimits valid]
  decide

theorem absent_period_check : nativeLimits (numericFields {sampleLimits with period := 1}) = true ∧
    limitsValid {sampleLimits with period := 1} = false := by
  simp only [nativeLimits, numericFields, sampleLimits, fieldAt, fieldCount, Nat.reduceAdd, Nat.reduceBEq, Bool.true_and, pageAligned_exact]
  decide

end LeanCageM4.Bounds
