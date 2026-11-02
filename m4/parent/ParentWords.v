(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-parent.history: Preserve actual observations and ordered source memory. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Ctypesdefs Cop Clight.
Require Import LocalAccess CallAccess.
From LeanCageMainNumber Require Import NumberControl.
From LeanCageMain Require Import Main MainStructure MainValues.
From LeanCageBounds Require Import BoundsStructure BoundsWords.
From LeanCageArguments Require Import ArgumentWords.
Open Scope Z_scope.
Lemma parent_local_value e le m b value : e!_parent=Some(b,tulong)->
 Mem.loadv Mint64 m(Vptr b Ptrofs.zero)=Some(Vlong(Int64.repr value))->
 expression_value main_ge e le m(Evar _parent tulong)(Vlong(Int64.repr value)).
Proof.
 intros LOCAL LOAD;eapply location_read_value;[apply local_location_value;exact LOCAL|].
 eapply deref_loc_value;[reflexivity|exact LOAD].
Qed.
Lemma parent_zero_operation m value : 0<=value<=Int64.max_unsigned->
 sem_unary_operation Onotbool(Vlong(Int64.repr value))tulong m=Some(Val.of_bool(value=?0)).
Proof. apply argument_empty_value. Qed.
Lemma parent_upper_operation m value : 0<=value<=Int64.max_unsigned->
 sem_binary_operation main_ge Ogt(Vlong(Int64.repr value))tulong(Vint(Int.repr 2147483647))tint m=
 Some(Val.of_bool(2147483647<?value)).
Proof. intros RANGE;exact(bounds_narrow_operation main_ge m upper value 2147483647 RANGE ltac:(lia)). Qed.
Lemma parent_narrow_cast m value : 0<=value<=Int64.max_unsigned->
 sem_cast(Vlong(Int64.repr value))tulong tint m=Some(Vint(Int.repr value)).
Proof.
 intros RANGE;change(Some(Vint(Int.repr(Int64.unsigned(Int64.repr value))))=Some(Vint(Int.repr value))).
 rewrite Int64.unsigned_repr by exact RANGE;reflexivity.
Qed.
Lemma parent_comparison m value observed :
 sem_binary_operation main_ge One(Vint observed)tint(Vint(Int.repr value))tint m=
 Some(Val.of_bool(negb(Int.eq observed(Int.repr value)))).
Proof. reflexivity. Qed.
Lemma parent_match_signed value observed : 0<value<=2147483647->
 Int.eq observed(Int.repr value)=true<->Int.signed observed=value.
Proof.
 intros RANGE;split.
 - intros EQ;pose proof(Int.eq_spec observed(Int.repr value))as SAME;rewrite EQ in SAME.
   rewrite SAME;apply Int.signed_repr;change(-2147483648<=value<=2147483647);lia.
 - intros EQ;rewrite<-EQ,Int.repr_signed;apply Int.eq_true.
Qed.
