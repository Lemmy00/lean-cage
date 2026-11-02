(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-parent.history: Preserve actual observations and ordered source memory. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From LeanCageMainNumber Require Import NumberControl.
From LeanCageMain Require Import Main MainStructure.
From LeanCageValidation Require Import StringRegion ValidationStructure ValidationValues.
From LeanCageParent Require Import ParentMachine ParentRegion ParentLift ParentPaths ParentStructure ParentComparison ParentFinish.
Import ListNotations.
Open Scope nat_scope.
Lemma parent_observe_call e le m k : e!_getppid=None->le!_t'13=Some(Val.of_bool false)->
 store_path main_ge(fun after=>after=m)
 (State f_main parent_observe(Kseq(selection_finish 15)(Kseq(selection_after 15)k))e le m)3
 (Callstate getppid_definition[](Kcall(Some _t'15)f_main e le(parent_observation_cont k))m).
Proof.
 intros GLOBAL FLAG;unfold parent_observe;compare_next.
 - eapply certified_if_edge with(v:=Val.of_bool false)(b:=false);[apply old_expression_value;apply value_temp;exact FLAG|reflexivity].
 - compare_route;unfold parent_call;compare_next.
   + eapply certified_call_edge.
     * reflexivity.
     * apply old_expression_value;eapply value_function;[exact GLOBAL|exact(proj1 getppid_binding)|reflexivity].
     * apply no_argument_values.
     * exact(proj2 getppid_binding).
     * reflexivity.
   + constructor;reflexivity.
Qed.
Lemma parent_observe_reject e le m k : le!_t'13=Some(Val.of_bool true)->
 store_path main_ge(fun after=>after=m)
 (State f_main parent_observe(Kseq(selection_finish 15)(Kseq(selection_after 15)k))e le m)6
 (parent_endpoint e(PTree.set _t'14(Vint Int.one)le)k m true).
Proof.
 intros FLAG;unfold parent_observe;compare_next.
 - eapply certified_if_edge with(v:=Val.of_bool true)(b:=true);[apply old_expression_value;apply value_temp;exact FLAG|reflexivity].
 - compare_next;[apply certified_set_edge;apply old_expression_value;apply value_int|].
   apply parent_finish_path with(bad:=true);apply PTree.gss.
Qed.
Theorem parent_observe_certificate cell e le m k output value :
 e!_getppid=None->e!_parent=Some(output,tulong)->le!_t'13=Some(Val.of_bool false)->
 (0<=value<=Int64.max_unsigned)%Z->Mem.loadv Mint64 m(Vptr output Ptrofs.zero)=Some(Vlong(Int64.repr value))->
 parent_certificate main_ge cell(fun after=>after=m)(parent_observed_frontier e le k m value)14
 (State f_main parent_observe(Kseq(selection_finish 15)(Kseq(selection_after 15)k))e le m).
Proof.
 intros GLOBAL LOCAL FLAG RANGE LOAD;change 14 with(3+11).
 eapply parent_store_path;[apply parent_observe_call;assumption|].
 apply parent_choice with(preferred:=Int.repr value);[reflexivity|].
 intros observed;apply parent_return_certificate with(output:=output);assumption.
Qed.
