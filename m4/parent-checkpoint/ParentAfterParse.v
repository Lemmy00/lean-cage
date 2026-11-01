(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.composition: Candidate source connection; integration review remains open. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess WriteAll.
From LeanCageMainNumber Require Import NumberStorage NumberControl.
From LeanCageMain Require Import Main MainStructure.
From LeanCageValidation Require Import StringRegion ValidationStructure ValidationValues.
From LeanCageParent Require Import ParentMachine ParentRegion ParentLift ParentPaths ParentStructure ParentParse ParentGuards ParentComparison ParentFinish ParentObserve ParentControl.
Import ListNotations.
Open Scope nat_scope.
Definition parent_frontier e base k m parsed s :=
 if parent_guard_bad parsed then
 exists final, validation_frame base final /\ s=parent_endpoint e final k m true
 else parent_observed_frontier e base k m(parent_value parsed)s.
Lemma parent_frontier_frame e base middle k m parsed s :
 validation_frame base middle->parent_frontier e middle k m parsed s->parent_frontier e base k m parsed s.
Proof.
 intros FRAME;unfold parent_frontier;destruct(parent_guard_bad parsed).
 - intros[final[TAIL END]];exists final;split;[eapply validation_frame_trans;eassumption|exact END].
 - intros[observed[final[TAIL[REG END]]]];exists observed,final;split;[eapply validation_frame_trans;eassumption|auto].
Qed.
Theorem parent_after_parse cell e le m k output parsed :
 (parent_guard_bad parsed=false->e!_getppid=None)->e!_parent=Some(output,tulong)->
 (forall value,parsed=Some value->(0<=value<=Int64.max_unsigned)%Z /\
 Mem.loadv Mint64 m(Vptr output Ptrofs.zero)=Some(Vlong(Int64.repr value)))->
 parent_certificate main_ge cell(fun after=>after=m)(parent_frontier e le k m parsed)28
 (Returnstate(number_code parsed)(parent_number_cont e le k)m).
Proof.
 intros GLOBAL LOCAL OWN;eapply parent_weaken with(n:=parent_guard_cost parsed+14);
 [|pose proof(parent_guard_cost_bound parsed);lia].
 eapply parent_store_path;[apply parent_to_observe_path with(output:=output);assumption|].
 eapply parent_convert with(R:=parent_frontier e(parent_guard_env le parsed)k m parsed).
 - unfold parent_frontier;pose proof(parent_guard_env_register le parsed)as REG.
   destruct(parent_guard_bad parsed)eqn:BAD.
   + eapply parent_weaken with(n:=6);[|lia].
     replace 6 with(6+0)by lia;eapply parent_store_path;[apply parent_observe_reject;exact REG|].
     apply parent_stop;[reflexivity|].
     exists(PTree.set _t'14(Vint Int.one)(parent_guard_env le parsed));split;[unfold validation_frame;split;WriteAll.lookup|reflexivity].
   + apply parent_observe_certificate with(output:=output);[apply GLOBAL;reflexivity|exact LOCAL|exact REG| |];
     destruct parsed as[value|];try discriminate BAD;
     exact(proj1(OWN value eq_refl))||exact(proj2(OWN value eq_refl)).
 - intros current SAME;exact SAME.
 - intros s END;apply parent_frontier_frame with(middle:=parent_guard_env le parsed);[apply parent_guard_env_frame|exact END].
Qed.
