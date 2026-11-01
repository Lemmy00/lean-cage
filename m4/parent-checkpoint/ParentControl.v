(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.composition: Candidate source connection; integration review remains open. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From LeanCageMainNumber Require Import NumberStorage NumberControl.
From LeanCageMain Require Import Main MainStructure.
From LeanCageValidation Require Import StringRegion ValidationStructure ValidationValues.
From LeanCageParent Require Import ParentStructure ParentParse ParentGuards ParentComparison ParentFinish.
Import ListNotations.
Open Scope nat_scope.
Definition parent_value parsed : Z := match parsed with None=>0%Z|Some value=>value end.
Definition parent_returned le parsed := PTree.set _t'11(number_code parsed)le.
Definition parent_guard_env le parsed := parent_upper_env(parent_zero_env(parent_returned le parsed)parsed)
 (parent_value parsed)(parent_zero_bad parsed).
Definition parent_guard_cost parsed := 4+(match parsed with None=>2|Some _=>5 end)+
 (if parent_zero_bad parsed then 2 else 5).
Lemma parent_guard_cost_bound parsed : parent_guard_cost parsed<=14.
Proof. unfold parent_guard_cost;destruct parsed;destruct(parent_zero_bad _);lia. Qed.
Lemma parent_guard_expansion parsed : parent_zero_bad parsed||(2147483647<?parent_value parsed)%Z=parent_guard_bad parsed.
Proof. destruct parsed;reflexivity. Qed.
Theorem parent_to_observe_path e le m k output parsed : e!_parent=Some(output,tulong)->
 (forall value,parsed=Some value->(0<=value<=Int64.max_unsigned)%Z /\
 Mem.loadv Mint64 m(Vptr output Ptrofs.zero)=Some(Vlong(Int64.repr value)))->
 store_path main_ge(fun after=>after=m)(Returnstate(number_code parsed)(parent_number_cont e le k)m)
 (parent_guard_cost parsed)
 (State f_main parent_observe(Kseq(selection_finish 15)(Kseq(selection_after 15)k))e(parent_guard_env le parsed)m).
Proof.
 intros LOCAL OWN;unfold parent_guard_cost,parent_guard_env,parent_number_cont,parent_parse_cont,parent_returned.
 replace(4+(match parsed with None=>2|Some _=>5 end)+(if parent_zero_bad parsed then 2 else 5))with
 (2+((match parsed with None=>2|Some _=>5 end)+(1+((if parent_zero_bad parsed then 2 else 5)+1))))by lia.
 compare_route;compare_route;eapply store_path_trans with(n:=match parsed with None=>2|Some _=>5 end).
 - apply parent_zero_path with(output:=output);[exact LOCAL|apply PTree.gss|exact OWN].
 - compare_route;eapply store_path_trans with(n:=if parent_zero_bad parsed then 2 else 5).
   + apply parent_upper_path with(output:=output)(value:=parent_value parsed)(bad:=parent_zero_bad parsed);[exact LOCAL|apply parent_zero_env_register|].
     intros BAD;destruct parsed as[value|];[apply OWN;reflexivity|discriminate BAD].
   + compare_route;constructor;reflexivity.
Qed.
Theorem parent_guard_env_register le parsed :
 (parent_guard_env le parsed)!_t'13=Some(Val.of_bool(parent_guard_bad parsed)).
Proof. unfold parent_guard_env;rewrite parent_upper_env_register,parent_guard_expansion;reflexivity. Qed.
Theorem parent_guard_env_frame le parsed : validation_frame le(parent_guard_env le parsed).
Proof.
 unfold parent_guard_env;eapply validation_frame_trans;[|apply parent_upper_env_frame].
 eapply validation_frame_trans;[apply parent_parsed_frame|apply parent_zero_env_frame].
Qed.
