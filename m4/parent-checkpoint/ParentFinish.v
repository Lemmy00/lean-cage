(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.composition: Candidate source connection; integration review remains open. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From LeanCageMainNumber Require Import NumberControl.
From LeanCageMain Require Import Main MainStructure.
From LeanCageValidation Require Import StringRegion ValidationStructure ValidationValues ValidationFinish.
From LeanCageParent Require Import ParentMachine ParentRegion ParentLift ParentStructure ParentWords ParentComparison.
Import ListNotations.
Open Scope nat_scope.
Definition parent_endpoint e le k m (bad:bool) := if bad then State f_main(selection_report 15)
 (Kseq(selection_report_rest 15)(Kseq(selection_return 15)(Kseq(selection_after 15)k)))e le m
 else State f_main(selection_after 15)k e le m.
Theorem parent_finish_path e le m k bad : le!_t'14=Some(Val.of_bool bad)->
 store_path main_ge(fun after=>after=m)(State f_main Sskip(Kseq(selection_finish 15)(Kseq(selection_after 15)k))e le m)
 (if bad then 4 else 3)(parent_endpoint e le k m bad).
Proof.
 intros REG;destruct bad;unfold parent_endpoint;compare_route;
 destruct(proj1(proj2 parent_source_structure))as[SHAPE FAILURE];rewrite SHAPE;compare_next.
 - eapply certified_if_edge with(v:=Val.of_bool true)(b:=true);[apply old_expression_value;apply value_temp;exact REG|reflexivity].
 - rewrite FAILURE;compare_route;compare_route;constructor;reflexivity.
 - eapply certified_if_edge with(v:=Val.of_bool false)(b:=false);[apply old_expression_value;apply value_temp;exact REG|reflexivity].
 - compare_route;constructor;reflexivity.
Qed.
Definition parent_return_env le value observed := parent_compared(PTree.set _t'15(Vint observed)le)value observed.
Theorem parent_return_path e le m k output value observed :
 e!_parent=Some(output,tulong)->(0<=value<=Int64.max_unsigned)%Z->
 Mem.loadv Mint64 m(Vptr output Ptrofs.zero)=Some(Vlong(Int64.repr value))->
 store_path main_ge(fun after=>after=m)
 (Returnstate(Vint observed)(Kcall(Some _t'15)f_main e le(parent_observation_cont k))m)
 (6+(if negb(Int.eq observed(Int.repr value))then 4 else 3))
 (parent_endpoint e(parent_return_env le value observed)k m(negb(Int.eq observed(Int.repr value)))).
Proof.
 intros LOCAL RANGE LOAD;unfold parent_observation_cont,parent_return_env.
 change(6+(if negb(Int.eq observed(Int.repr value))then 4 else 3))with
 (2+(4+(if negb(Int.eq observed(Int.repr value))then 4 else 3))).
 compare_route;compare_route;eapply store_path_trans with(n:=4).
 - apply parent_comparison_path with(output:=output);[exact LOCAL|apply PTree.gss|exact RANGE|exact LOAD].
 - apply parent_finish_path;exact(proj2(parent_comparison_registers _ value observed(PTree.gss _ _ _))).
Qed.
Definition parent_observed_frontier e base k m value s := exists observed final,
 validation_frame base final /\final!_t'15=Some(Vint observed) /\
 s=parent_endpoint e final k m(negb(Int.eq observed(Int.repr value))).
Theorem parent_return_certificate cell e le m k output value observed :
 e!_parent=Some(output,tulong)->(0<=value<=Int64.max_unsigned)%Z->
 Mem.loadv Mint64 m(Vptr output Ptrofs.zero)=Some(Vlong(Int64.repr value))->
 parent_certificate main_ge cell(fun after=>after=m)(parent_observed_frontier e le k m value)10
 (Returnstate(Vint observed)(Kcall(Some _t'15)f_main e le(parent_observation_cont k))m).
Proof.
 intros LOCAL RANGE LOAD;apply parent_from_string.
 eapply region_weaken with(n:=6+(if negb(Int.eq observed(Int.repr value))then 4 else 3));
 [|destruct(negb(Int.eq observed(Int.repr value)));lia].
 replace(6+(if negb(Int.eq observed(Int.repr value))then 4 else 3))with
 ((6+(if negb(Int.eq observed(Int.repr value))then 4 else 3))+0)at 1 by lia.
 eapply region_store_path;[apply parent_return_path with(output:=output);assumption|].
 apply region_stop;[unfold parent_endpoint;destruct(negb(Int.eq observed(Int.repr value)));reflexivity|].
 exists observed,(parent_return_env le value observed);split.
 - unfold parent_return_env;eapply validation_frame_trans;[|apply parent_comparison_frame].
   unfold validation_frame;split;WriteAll.lookup.
 - split;[unfold parent_return_env;exact(proj1(parent_comparison_registers _ value observed(PTree.gss _ _ _)))|reflexivity].
Qed.
