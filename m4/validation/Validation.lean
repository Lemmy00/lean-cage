-- SPDX-License-Identifier: Apache-2.0
-- §AR-m4-controller.strings: Exact byte predicates and the live native plan.
import Digest
namespace LeanCageM4.Validation
open LeanCageM3 LeanCageM4.Plan LeanCageM4.Digest

def bytesEq (xs ys : List Nat) : Bool :=
  match xs, ys with
  | [], [] => true
  | a :: xs, b :: ys => (a == b) && bytesEq xs ys
  | [], _ :: _ => false
  | _ :: _, [] => false
termination_by structural xs

def noneBytes : List Nat := [110, 111, 110, 101]
def discardBytes : List Nat := [100, 105, 115, 99, 97, 114, 100]
def filesBytes : List Nat := [114, 101, 103, 117, 108, 97, 114, 45, 102, 105, 108, 101, 115]
def shellBytes : List Nat := [47, 98, 105, 110, 47, 115, 104]
def pythonBytes : List Nat := [47, 117, 115, 114, 47, 108, 111, 99, 97, 108, 47, 98, 105, 110, 47, 112, 121, 116, 104, 111, 110, 51]
def planBytes : List Nat := [77, 51, 80, 76, 65, 78, 49]
def checkBytes : List Nat := [77, 51, 67, 72, 69, 67, 75, 49]

def nativeStringCheck : Nat → Nat → List Nat → Bool
  | Nat.zero, argc, bytes => (17 ≤ argc) && (bytesEq bytes planBytes || bytesEq bytes checkBytes)
  | Nat.succ Nat.zero, _, bytes => bytesEq bytes discardBytes || bytesEq bytes filesBytes
  | Nat.succ (Nat.succ Nat.zero), _, bytes => bytesEq bytes noneBytes || nativeDigestBytes bytes
  | Nat.succ (Nat.succ (Nat.succ Nat.zero)), _, bytes => bytesEq bytes shellBytes || bytesEq bytes pythonBytes
  | Nat.succ (Nat.succ (Nat.succ (Nat.succ _))), _, _ => false

def utf8 (text : String) : List Nat := text.toUTF8.data.toList.map UInt8.toNat

theorem bytesEq_exact (xs ys : List Nat) : bytesEq xs ys = true ↔ xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [bytesEq]
  | cons x xs ih => cases ys <;> simp [bytesEq, ih]

theorem mode_exact (argc : Nat) (bytes : List Nat) :
    nativeStringCheck 0 argc bytes = true ↔ 17 ≤ argc ∧ (bytes = planBytes ∨ bytes = checkBytes) := by
  simp [nativeStringCheck, bytesEq_exact]

theorem export_exact (argc : Nat) (bytes : List Nat) :
    nativeStringCheck 1 argc bytes = true ↔ bytes = discardBytes ∨ bytes = filesBytes := by
  simp [nativeStringCheck, bytesEq_exact]

theorem digest_option_exact (argc : Nat) (bytes : List Nat) :
    nativeStringCheck 2 argc bytes = true ↔ bytes = noneBytes ∨ nativeDigestBytes bytes = true := by
  simp [nativeStringCheck, bytesEq_exact]

theorem executable_exact (argc : Nat) (bytes : List Nat) :
    nativeStringCheck 3 argc bytes = true ↔ bytes = shellBytes ∨ bytes = pythonBytes := by
  simp [nativeStringCheck, bytesEq_exact]

theorem literal_utf8 : utf8 "none" = noneBytes ∧ utf8 "discard" = discardBytes ∧
    utf8 "regular-files" = filesBytes ∧ utf8 "/bin/sh" = shellBytes ∧
    utf8 "/usr/local/bin/python3" = pythonBytes ∧ utf8 "M3PLAN1" = planBytes ∧
    utf8 "M3CHECK1" = checkBytes := by decide

theorem live_mode (executable : String) (p : Policy) (pid : Nat) (pre : Bool)
    (valid : argvValid p.argv = true) :
    ((nativeArgs executable p pid pre)[1]?).map
      (fun s => nativeStringCheck 0 (nativeArgs executable p pid pre).size (utf8 s)) = some true := by
  rw [native_mode]
  apply congrArg some
  apply (mode_exact _ _).2
  refine ⟨(native_count_valid executable p pid pre valid).1, ?_⟩
  cases pre <;> decide

theorem live_export (executable : String) (p : Policy) (pid : Nat) (pre : Bool) :
    ((nativeArgs executable p pid pre)[13]?).map
      (fun s => nativeStringCheck 1 (nativeArgs executable p pid pre).size (utf8 s)) = some true := by
  rw [native_export]
  apply congrArg some
  apply (export_exact _ _).2
  cases p.exportFiles <;> decide

theorem parsed_digest_option (j : Lean.Json) (name : String) (value : Option String) (argc : Nat)
    (parsed : liveDigestField j name = .ok value) :
    nativeStringCheck 2 argc (utf8 ((value.map (fun s => (s.drop 7).toString)).getD "none")) = true := by
  apply (digest_option_exact _ _).2
  cases value with
  | none => left; decide
  | some text => right; exact parsed_digest_bytes j name text parsed

theorem live_workspace_option (executable : String) (p : Policy) (pid : Nat) (pre : Bool)
    (j : Lean.Json) (name : String) (parsed : liveDigestField j name = .ok p.workspaceInput) :
    ((nativeArgs executable p pid pre)[14]?).map
      (fun s => nativeStringCheck 2 (nativeArgs executable p pid pre).size (utf8 s)) = some true := by
  rw [(native_digests executable p pid pre).1]
  exact congrArg some (parsed_digest_option j name p.workspaceInput _ parsed)

theorem live_stdin_option (executable : String) (p : Policy) (pid : Nat) (pre : Bool)
    (j : Lean.Json) (name : String) (parsed : liveDigestField j name = .ok p.stdinInput) :
    ((nativeArgs executable p pid pre)[15]?).map
      (fun s => nativeStringCheck 2 (nativeArgs executable p pid pre).size (utf8 s)) = some true := by
  rw [(native_digests executable p pid pre).2]
  exact congrArg some (parsed_digest_option j name p.stdinInput _ parsed)

theorem argv_head_allowed (argv : Array String) (valid : argvValid argv = true) :
    nativeStringCheck 3 (16 + argv.size) (utf8 (argv[0]?.getD "")) = true := by
  simp only [argvValid, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at valid
  apply (executable_exact _ _).2
  rcases valid.1.1.2 with shell | python
  · rw [shell]; left; decide
  · rw [python]; right; decide

theorem native_guest_first (executable : String) (p : Policy) (pid : Nat) (pre : Bool) :
    (nativeArgs executable p pid pre)[16]? = p.argv[0]? := by
  simp [nativeArgs, planArgs, Array.getElem?_append]

theorem live_executable (executable : String) (p : Policy) (pid : Nat) (pre : Bool)
    (valid : argvValid p.argv = true) :
    ((nativeArgs executable p pid pre)[16]?).map
      (fun s => nativeStringCheck 3 (nativeArgs executable p pid pre).size (utf8 s)) = some true := by
  rw [native_guest_first, native_argument_count]
  have allowed := argv_head_allowed p.argv valid
  cases head : p.argv[0]? with
  | none => simp [argvValid, head] at valid
  | some text => simpa [head] using congrArg some allowed

theorem parsed_option_memory_shape (j : Lean.Json) (name : String) (value : Option String)
    (parsed : liveDigestField j name = .ok value) :
    let text := (value.map (fun s => (s.drop 7).toString)).getD "none"
    text.utf8ByteSize ≤ 64 ∧ (0 : UInt8) ∉ text.toUTF8.data.toList := by
  cases value with
  | none => decide
  | some text =>
    have shape := parsed_digest_memory_shape j name text parsed
    exact ⟨Nat.le_of_eq shape.1, shape.2⟩

end LeanCageM4.Validation
