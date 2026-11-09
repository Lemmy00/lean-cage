(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Identify reusable source procedures and reject vacuous variadic call sites. *)
From Stdlib Require Import List Bool PArith.
From compcert Require Import AST Ctypes Cop Clight.
Require Import Slice.
From EntryNative Require Import EntrySource NativeHandoffMachine.
Import ListNotations.

Theorem current_entry_failure_exact : EntrySource.f_fail_child = Slice.f_fail_child.
Proof. reflexivity. Qed.

Theorem current_entry_write_all_exact : EntrySource.f_write_all = Slice.f_write_all.
Proof. reflexivity. Qed.

Theorem current_entry_error_number_exact : EntrySource.f_error_number = Slice.f_error_number.
Proof. reflexivity. Qed.

Theorem current_entry_put32_exact : EntrySource.f_put32 = Slice.f_put32.
Proof. reflexivity. Qed.

Definition entry_source_definition (id : ident) :=
  find (fun item => Pos.eqb (fst item) id) (prog_defs EntrySource.prog).

Theorem current_entry_decimal_signature : entry_source_definition EntrySource._entry_decimal =
  Some (EntrySource._entry_decimal, Gfun entry_decimal_definition).
Proof. reflexivity. Qed.

Theorem current_entry_flags_signature : entry_source_definition EntrySource._entry_descriptor_flags =
  Some (EntrySource._entry_descriptor_flags, Gfun entry_flags_definition).
Proof. reflexivity. Qed.

Theorem current_entry_exec_signature : entry_source_definition EntrySource._execve =
  Some (EntrySource._execve, Gfun entry_exec_definition).
Proof. reflexivity. Qed.

(* The source semantics does not evaluate extra variadic arguments.  A length
   mismatch is an ill-supported source path, never evidence that the path is
   safe.  The handoff uses nonvariadic primitive adapters and numeric readback. *)
Fixpoint handoff_call_arities (statement : statement) : bool :=
  match statement with
  | Scall _ function arguments =>
      match classify_fun (typeof function) with
      | fun_case_f parameters _ _ => Nat.eqb (length arguments) (length parameters)
      | _ => false
      end
  | Ssequence first second | Sloop first second =>
      handoff_call_arities first && handoff_call_arities second
  | Sifthenelse _ yes no => handoff_call_arities yes && handoff_call_arities no
  | Sswitch _ branches => handoff_branch_arities branches
  | Slabel _ body => handoff_call_arities body
  | _ => true
  end
with handoff_branch_arities (branches : labeled_statements) : bool :=
  match branches with
  | LSnil => true
  | LScons _ statement rest => handoff_call_arities statement && handoff_branch_arities rest
  end.

Theorem current_entry_handoff_call_arities :
  handoff_call_arities (fn_body EntrySource.f_guest) = true.
Proof. reflexivity. Qed.

Theorem handoff_evaluated_argument_lengths ge e le m arguments parameters values :
  eval_exprlist ge e le m arguments parameters values ->
  length arguments = length parameters /\ length values = length parameters.
Proof. intros EVALUATED; induction EVALUATED; cbn; intuition congruence. Qed.
