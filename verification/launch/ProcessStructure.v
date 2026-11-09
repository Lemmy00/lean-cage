(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Check structural interfaces against the complete maintained source AST. *)
From Stdlib Require Import List.
From compcert Require Import Integers AST Ctypes Ctypesdefs Clight.
From EntryNative Require Import EntrySource NativeHandoffBindings.
Import ListNotations.

Fixpoint admission_tail (index : nat) (body : statement) : statement :=
  match index, body with
  | O, _ => body
  | S rest, Ssequence _ body => admission_tail rest body
  | _, _ => Sskip
  end.

Definition admission_phase index :=
  match admission_tail index (fn_body f_admit_child) with
  | Ssequence first _ => first
  | last => last
  end.

Definition admission_wait := admission_phase 0.
Definition admission_identity := admission_phase 1.
Definition admission_stopped := admission_phase 2.
Definition admission_stopsig := admission_phase 3.
Definition admission_format := admission_phase 4.
Definition admission_positive_length := admission_phase 5.
Definition admission_bounded_length := admission_phase 6.
Definition admission_leading_digit := admission_phase 7.
Definition admission_number := admission_phase 8.
Definition admission_pid_equal := admission_phase 9.
Definition admission_place := admission_phase 10.
Definition admission_options := admission_phase 11.
Definition admission_return := admission_phase 12.
Definition admission_failure := Sreturn (Some (Eunop Cop.Oneg (Econst_int Int.one tint) tint)).

Theorem admission_source_phases : fn_body f_admit_child =
  Ssequence admission_wait (Ssequence admission_identity
    (Ssequence admission_stopped (Ssequence admission_stopsig
      (Ssequence admission_format (Ssequence admission_positive_length
        (Ssequence admission_bounded_length (Ssequence admission_leading_digit
          (Ssequence admission_number (Ssequence admission_pid_equal
            (Ssequence admission_place (Ssequence admission_options admission_return))))))))))).
Proof. reflexivity. Qed.

Theorem admission_finish_source : admission_return = Sreturn (Some (Econst_int Int.zero tint)).
Proof. reflexivity. Qed.

Theorem admission_numeric_source : admission_tail 5 (fn_body f_admit_child) =
  Ssequence admission_positive_length (Ssequence admission_bounded_length
    (Ssequence admission_leading_digit (Ssequence admission_number
      (Ssequence admission_pid_equal (admission_tail 10 (fn_body f_admit_child)))))).
Proof. reflexivity. Qed.

Theorem admission_helper_call_arities :
  handoff_call_arities (fn_body f_admit_child) = true.
Proof. vm_compute; reflexivity. Qed.

Theorem namespace_direct_call_arities :
  handoff_call_arities (fn_body f_namespace_init) = true.
Proof. vm_compute; reflexivity. Qed.
