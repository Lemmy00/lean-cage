(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.bounds: Actual expression values for policy guards and argument totals. *)
From Stdlib Require Import ZArith Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Ctypesdefs Cop Clight.
Require Import ClightSteps LocalAccess.
From LeanCageMainNumber Require Import NumberStructure NumberControl.
From LeanCageMain Require Import Main MainStructure.
From LeanCageBounds Require Import BoundsStructure BoundsWords.
Open Scope Z_scope.
Lemma guard_expression_value ge e le m g x : guard_valid g ->
 0<=x<=Int64.max_unsigned -> le!(guard_read g)=Some(Vlong(Int64.repr x)) ->
 expression_value ge e le m
 (Ecast(Ebinop(guard_operator g)(Etempvar(guard_read g)tulong)
  (guard_constant g)(guard_type g))tbool)(Val.of_bool(guard_bad g x)).
Proof.
 intros[FIELD[POS BOUND]]X REG.
 eapply cast_expression_value with(v:=bound_operation_value(guard_kind g)x(guard_bound g)).
 - unfold guard_constant;destruct(guard_wide g)eqn:W.
   + eapply binary_expression_value.
     * apply old_expression_value;apply value_temp;exact REG.
     * apply long_expression_value.
     * apply bounds_machine_operation;[exact X|change Int64.max_unsigned with 18446744073709551615;lia].
   + eapply binary_expression_value.
     * apply old_expression_value;apply value_temp;exact REG.
     * apply old_expression_value;apply value_int.
     * apply bounds_narrow_operation;[exact X|lia].
 - apply bounds_operation_cast;[exact X|change Int64.max_unsigned with 18446744073709551615;
   destruct(guard_wide g);cbn in BOUND;lia].
Qed.
Lemma bounds_count_value ge e le m argc : 17<=argc<=2147483647 ->
 le!_argc=Some(Vint(Int.repr argc)) ->
 expression_value ge e le m
 (Ebinop Ogt(Ebinop Osub(Etempvar _argc tint)(Econst_int(Int.repr 16)tint)tint)
 (Econst_int(Int.repr 64)tint)tint)(Val.of_bool(64<?argc-16)).
Proof.
 intros RANGE REG;eapply binary_expression_value.
 - eapply binary_expression_value.
   + apply old_expression_value;apply value_temp;exact REG.
   + apply old_expression_value;apply value_int.
   + apply bounds_argc_sub;exact RANGE.
 - apply old_expression_value;apply value_int.
 - apply bounds_argc_cmp;exact RANGE.
Qed.
Lemma bounds_bytes_value ge e le m bytes : 0<=bytes<=Int64.max_unsigned ->
 le!_bytes=Some(Vlong(Int64.repr bytes)) ->
 expression_value ge e le m
 (Ecast(Ebinop Ogt(Etempvar _bytes tulong)(Econst_int(Int.repr 16384)tint)tint)tbool)
 (Val.of_bool(16384<?bytes)).
Proof.
 intros RANGE REG;eapply cast_expression_value.
 - eapply binary_expression_value.
   + apply old_expression_value;apply value_temp;exact REG.
   + apply old_expression_value;apply value_int.
   + apply bounds_narrow_operation with(kind:=upper);[exact RANGE|lia].
 - apply number_bool_cast.
Qed.
