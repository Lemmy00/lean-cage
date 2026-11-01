(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.decimal: Exact source parsing, memory behavior and interruption. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess WriteAll.
From LeanCageController Require Import NumberSlice.
Import ListNotations.
Open Scope Z_scope.
Definition number_loop := match fn_body f_number with
 | Ssequence _ (Ssequence _ (Ssequence (Ssequence _ loop) _)) => loop | _ => Sskip end.
Definition number_loop_body := match number_loop with Sloop body _ => body | _ => Sskip end.
Definition number_increment := match number_loop with Sloop _ inc => inc | _ => Sskip end.
Definition number_finish := match fn_body f_number with
 | Ssequence _ (Ssequence _ (Ssequence _ finish)) => finish | _ => Sskip end.
Definition number_prefix := match fn_body f_number with Ssequence pre _ => pre | _ => Sskip end.
Definition number_suffix := match fn_body f_number with Ssequence _ post => post | _ => Sskip end.
Definition number_initial text output k m := Callstate (Internal f_number) [text;output] k m.
Definition number_env text output := PTree.set _value output
 (PTree.set _text text (create_undef_temps (fn_temps f_number))).
Lemma number_loop_structure : number_loop = Sloop number_loop_body number_increment.
Proof. reflexivity. Qed.
Lemma number_body_structure : fn_body f_number = Ssequence number_prefix number_suffix.
Proof. reflexivity. Qed.
Lemma number_entry ge text output k m :
 store_edge ge (number_initial text output k m)
 (State f_number (fn_body f_number) k empty_env (number_env text output) m).
Proof.
 apply function_entry_source_edge. constructor.
 - constructor.
 - repeat constructor; simpl; intuition discriminate.
 - unfold list_disjoint, var_names; simpl; intros x y A B;
   repeat match goal with H : _ \/ _ |- _ => destruct H end; try contradiction; subst; discriminate.
 - constructor.
 - reflexivity.
Qed.
Lemma long_expression_value ge e le m i ty :
 expression_value ge e le m (Econst_long i ty) (Vlong i).
Proof.
 split; [constructor|]. intros other EV; inversion EV; subst; [reflexivity|].
 match goal with H : eval_lvalue _ _ _ _ _ _ _ _ |- _ => inversion H end.
Qed.
Ltac number_expression := first
 [ apply long_expression_value
 | eapply binary_expression_value; [number_expression|number_expression|try reflexivity]
 | eapply cast_expression_value; [number_expression|try reflexivity]
 | apply old_expression_value; WriteAll.expression ].
Definition number_first s := match s with Ssequence a _ => a | _ => Sskip end.
Definition number_second s := match s with Ssequence _ b => b | _ => Sskip end.
Definition number_guard := number_first number_loop_body.
Definition number_checks := number_first (number_second number_loop_body).
Definition number_reject := number_second number_checks.
Definition number_digit_test := number_first (number_first number_checks).
Definition number_overflow_test := number_second (number_first number_checks).
Definition number_update := number_second (number_second number_loop_body).
Definition number_overflow_expression := match number_overflow_test with
 | Sifthenelse _ _ (Ssequence _ (Sset _ (Ecast a _))) => a
 | _ => Econst_int Int.zero tint end.
Definition number_update_expression := match number_update with
 | Ssequence _ (Sset _ a) => a | _ => Econst_int Int.zero tint end.
Lemma number_loop_body_structure : number_loop_body =
 Ssequence number_guard (Ssequence (Ssequence (Ssequence number_digit_test number_overflow_test) number_reject) number_update).
Proof. reflexivity. Qed.
Ltac number_unfold s := let body := eval cbv [number_guard number_checks number_reject
 number_digit_test number_overflow_test number_update number_overflow_expression
 number_update_expression number_prefix number_suffix number_finish number_loop
 number_loop_body number_increment number_first number_second f_number] in s in change s with body.
