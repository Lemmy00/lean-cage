(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.arguments: Typed evaluation of the actual loop's expressions. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import ClightSteps LocalAccess CallAccess WriteAll.
From LeanCageMainNumber Require Import NumberControl.
From LeanCageMain Require Import Main MainStructure MainValues.
From LeanCageArguments Require Import ArgumentArithmetic ArgumentWords.
Import ListNotations.
Open Scope Z_scope.
Definition argument_registers le argv ofs argc i total :=
 le!_argv=Some(Vptr argv ofs) /\ le!_argc=Some(Vint(Int.repr argc)) /\
 le!_i__1=Some(Vint(Int.repr i)) /\ le!_bytes=Some(Vlong(Int64.repr total)).
Lemma argument_pointer_value e le m argv ofs i :
 le!_argv=Some(Vptr argv ofs) -> le!_i__1=Some(Vint(Int.repr i)) -> 0<=i<=2147483647 ->
 expression_value main_ge e le m
 (Ebinop Oadd(Etempvar _argv(tptr(tptr tschar)))(Etempvar _i__1 tint)(tptr(tptr tschar)))
 (Vptr argv(Ptrofs.add ofs(Ptrofs.repr(8*i)))).
Proof.
 intros ARGV INDEX RANGE;eapply binary_expression_value.
 - apply old_expression_value;apply value_temp;exact ARGV.
 - apply old_expression_value;apply value_temp;exact INDEX.
 - apply argument_pointer_add;exact RANGE.
Qed.
Lemma argument_test_value e le m i argc :
 le!_i__1=Some(Vint(Int.repr i)) -> le!_argc=Some(Vint(Int.repr argc)) ->
 0<=i<=argc -> argc<=2147483647 ->
 expression_value main_ge e le m(Ebinop Olt(Etempvar _i__1 tint)(Etempvar _argc tint)tint)
 (Val.of_bool(i<?argc)).
Proof.
 intros INDEX ARGC RANGE HIGH;eapply binary_expression_value.
 - apply old_expression_value;apply value_temp;exact INDEX.
 - apply old_expression_value;apply value_temp;exact ARGC.
 - apply argument_index_test;assumption.
Qed.
Lemma argument_empty_expression e le m n : le!_n=Some(Vlong(Int64.repr n)) ->
 0<=n<=Int64.max_unsigned ->
 expression_value main_ge e le m(Eunop Onotbool(Etempvar _n tulong)tint)(Val.of_bool(n=?0)).
Proof.
 intros REG RANGE;apply old_expression_value;eapply value_unary;
 [apply value_temp;exact REG|apply argument_empty_value;exact RANGE].
Qed.
Lemma argument_size_expression e le m n : le!_n=Some(Vlong(Int64.repr n)) ->
 0<=n<=Int64.max_unsigned ->
 expression_value main_ge e le m
 (Ecast(Ebinop Ogt(Etempvar _n tulong)(Econst_int(Int.repr 4096)tint)tint)tbool)
 (Val.of_bool(4096<?n)).
Proof.
 intros REG RANGE;eapply cast_expression_value.
 - eapply binary_expression_value;
   [apply old_expression_value;apply value_temp;exact REG|apply old_expression_value;apply value_int|apply argument_size_value;exact RANGE].
 - apply number_bool_cast.
Qed.
Lemma argument_sum_expression e le m n total :
 le!_n=Some(Vlong(Int64.repr n)) -> le!_bytes=Some(Vlong(Int64.repr total)) ->
 0<=total -> 1<=n<=4096 -> total+n+1<=Int64.max_unsigned ->
 expression_value main_ge e le m
 (Ebinop Oadd(Etempvar _bytes tulong)
 (Ebinop Oadd(Etempvar _n tulong)(Econst_int(Int.repr 1)tint)tulong)tulong)
 (Vlong(Int64.repr(total+n+1))).
Proof.
 intros N TOTAL LOW SIZE HIGH;eapply binary_expression_value.
 - apply old_expression_value;apply value_temp;exact TOTAL.
 - eapply binary_expression_value;
   [apply old_expression_value;apply value_temp;exact N|apply old_expression_value;apply value_int|apply argument_size_plus_nul;exact SIZE].
 - apply argument_total_add_exact;assumption.
Qed.
