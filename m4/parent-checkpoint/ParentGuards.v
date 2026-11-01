(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.composition: Candidate source connection; integration review remains open. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From LeanCageMainNumber Require Import NumberStorage NumberControl.
From LeanCageMain Require Import Main MainStructure.
From LeanCageValidation Require Import ValidationValues.
From LeanCageParent Require Import ParentStructure ParentWords.
Import ListNotations.
Open Scope nat_scope.
Definition parent_zero_bad parsed := match parsed with None=>true|Some value=>(value=?0)%Z end.
Definition parent_zero_env le parsed := match parsed with
 |None=>PTree.set _t'12(Vint Int.one)le
 |Some value=>PTree.set _t'12(Val.of_bool(value=?0)%Z)(PTree.set _t'290(Vlong(Int64.repr value))le)end.
Ltac guard_next := eapply store_next;[reflexivity| |].
Ltac guard_route := guard_next;[apply unchanged_store_edge;WriteAll.structural|].
Theorem parent_zero_path e le m k output parsed : e!_parent=Some(output,tulong)->le!_t'11=Some(number_code parsed)->
 (forall value,parsed=Some value->(0<=value<=Int64.max_unsigned)%Z /\
 Mem.loadv Mint64 m(Vptr output Ptrofs.zero)=Some(Vlong(Int64.repr value)))->
 store_path main_ge(fun after=>after=m)(State f_main parent_zero k e le m)
 (match parsed with None=>2|Some _=>5 end)(State f_main Sskip k e(parent_zero_env le parsed)m).
Proof.
 intros LOCAL REG OWN;destruct parsed as[value|];unfold parent_zero,parent_zero_env.
 - destruct(OWN value eq_refl)as[RANGE LOAD];guard_next.
   + eapply certified_if_edge with(v:=Vint Int.zero)(b:=false);[apply old_expression_value;apply value_temp;exact REG|reflexivity].
   + guard_route;guard_next.
     * apply certified_set_edge;eapply parent_local_value;eassumption.
     * guard_route;guard_next.
       -- apply certified_set_edge;eapply cast_expression_value;[|apply number_bool_cast].
          apply old_expression_value;eapply value_unary;[apply value_temp;apply PTree.gss|apply parent_zero_operation;exact RANGE].
       -- constructor;reflexivity.
 - guard_next.
   + eapply certified_if_edge with(v:=Vint Int.mone)(b:=true);[apply old_expression_value;apply value_temp;exact REG|reflexivity].
   + guard_next;[apply certified_set_edge;apply old_expression_value;apply value_int|constructor;reflexivity].
Qed.
Lemma parent_zero_env_register le parsed : (parent_zero_env le parsed)!_t'12=Some(Val.of_bool(parent_zero_bad parsed)).
Proof. destruct parsed;unfold parent_zero_env,parent_zero_bad;apply PTree.gss. Qed.
Lemma parent_zero_env_frame le parsed : validation_frame le(parent_zero_env le parsed).
Proof. destruct parsed;unfold validation_frame,parent_zero_env;split;WriteAll.lookup. Qed.
Definition parent_upper_env le value (bad:bool) := if bad then PTree.set _t'13(Vint Int.one)le
 else PTree.set _t'13(Val.of_bool(2147483647<?value)%Z)(PTree.set _t'289(Vlong(Int64.repr value))le).
Theorem parent_upper_path e le m k output value bad : e!_parent=Some(output,tulong)->le!_t'12=Some(Val.of_bool bad)->
 (bad=false->(0<=value<=Int64.max_unsigned)%Z /\
 Mem.loadv Mint64 m(Vptr output Ptrofs.zero)=Some(Vlong(Int64.repr value)))->
 store_path main_ge(fun after=>after=m)(State f_main parent_upper k e le m)
 (if bad then 2 else 5)(State f_main Sskip k e(parent_upper_env le value bad)m).
Proof.
 intros LOCAL REG OWN;destruct bad;unfold parent_upper,parent_upper_env.
 - guard_next.
   + eapply certified_if_edge with(v:=Val.of_bool true)(b:=true);[apply old_expression_value;apply value_temp;exact REG|reflexivity].
   + guard_next;[apply certified_set_edge;apply old_expression_value;apply value_int|constructor;reflexivity].
 - destruct(OWN eq_refl)as[RANGE LOAD];guard_next.
   + eapply certified_if_edge with(v:=Val.of_bool false)(b:=false);[apply old_expression_value;apply value_temp;exact REG|reflexivity].
   + guard_route;guard_next.
     * apply certified_set_edge;eapply parent_local_value;eassumption.
     * guard_route;guard_next.
       -- apply certified_set_edge;eapply cast_expression_value;[|apply number_bool_cast].
          eapply binary_expression_value;
          [apply old_expression_value;apply value_temp;apply PTree.gss|apply old_expression_value;apply value_int|apply parent_upper_operation;exact RANGE].
       -- constructor;reflexivity.
Qed.
Lemma parent_upper_env_register le value bad :
 (parent_upper_env le value bad)!_t'13=Some(Val.of_bool(bad||(2147483647<?value)%Z)).
Proof. destruct bad;unfold parent_upper_env;cbn[orb];apply PTree.gss. Qed.
Lemma parent_upper_env_frame le value bad : validation_frame le(parent_upper_env le value bad).
Proof. destruct bad;unfold validation_frame,parent_upper_env;split;WriteAll.lookup. Qed.
