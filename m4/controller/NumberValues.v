(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.decimal: Exact source parsing, memory behavior and interruption. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Readers Machine ClightSteps LocalAccess CallAccess WriteAll.
From LeanCageController Require Import NumberSlice NumberStructure NumberMath NumberWords.
Open Scope Z_scope.
Lemma number_overflow_value ge e le m acc b :
 le ! _result = Some(Vlong(Int64.repr acc)) ->
 le ! _t'4 = Some(Vint(byte_word b)) ->
 expression_value ge e le m number_overflow_expression
 (Val.of_bool (Int64.ltu (number_machine_threshold b) (Int64.repr acc))).
Proof.
 intros ACC BYTE.
 unfold number_overflow_expression,number_overflow_test,number_checks,number_second,number_first,
 number_loop_body,number_loop,f_number.
 number_expression.
Qed.
Lemma number_update_value ge e le m acc b :
 le ! _result = Some(Vlong(Int64.repr acc)) ->
 le ! _t'3 = Some(Vint(byte_word b)) ->
 expression_value ge e le m number_update_expression (Vlong(number_machine_update acc b)).
Proof.
 intros ACC BYTE.
 unfold number_update_expression,number_update,number_second,number_loop_body,number_loop,f_number.
 number_expression.
Qed.
