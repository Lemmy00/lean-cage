(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-parent.history: Preserve actual observations and ordered source memory. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From LeanCageMainNumber Require Import NumberControl.
From LeanCageMain Require Import Main MainStructure.
From LeanCageValidation Require Import StringRegion ValidationStructure ValidationValues ValidationFinish.
From LeanCageParent Require Import ParentMachine ParentRegion ParentLift ParentStructure ParentWords.
Import ListNotations.
Open Scope nat_scope.
Definition parent_compared le value observed := PTree.set _t'14(Val.of_bool(negb(Int.eq observed(Int.repr value))))
 (PTree.set _t'288(Vlong(Int64.repr value))le).
Ltac compare_next := eapply store_next;[reflexivity| |].
Ltac compare_route := compare_next;[apply unchanged_store_edge;WriteAll.structural|].
Theorem parent_comparison_path e le m k output value observed :
 e!_parent=Some(output,tulong)->le!_t'15=Some(Vint observed)->(0<=value<=Int64.max_unsigned)%Z->
 Mem.loadv Mint64 m(Vptr output Ptrofs.zero)=Some(Vlong(Int64.repr value))->
 store_path main_ge(fun after=>after=m)(State f_main parent_compare k e le m)4
 (State f_main Sskip k e(parent_compared le value observed)m).
Proof.
 intros LOCAL OBSERVED RANGE LOAD;unfold parent_compare,parent_compared;compare_route;compare_next.
 - apply certified_set_edge;eapply parent_local_value;eassumption.
 - compare_route;compare_next.
   + apply certified_set_edge;eapply cast_expression_value;[|apply number_bool_cast].
     eapply binary_expression_value.
     * apply old_expression_value;apply value_temp;WriteAll.lookup.
     * eapply cast_expression_value;[apply old_expression_value;apply value_temp;apply PTree.gss|apply parent_narrow_cast;exact RANGE].
     * apply parent_comparison.
   + constructor;reflexivity.
Qed.
Theorem parent_comparison_frame le value observed : validation_frame le(parent_compared le value observed).
Proof. unfold validation_frame,parent_compared;split;WriteAll.lookup. Qed.
Theorem parent_comparison_registers le value observed : le!_t'15=Some(Vint observed)->
 (parent_compared le value observed)!_t'15=Some(Vint observed) /\
 (parent_compared le value observed)!_t'14=Some(Val.of_bool(negb(Int.eq observed(Int.repr value)))).
Proof. intros OBS;unfold parent_compared;split;WriteAll.lookup. Qed.
