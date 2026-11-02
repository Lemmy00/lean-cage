(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-parent.history: Preserve actual observations and ordered source memory. *)
From Stdlib Require Import List Lia.
From compcert Require Import AST Values Memory Clight.
Require Import Machine StoreSteps.
From LeanCageValidation Require Import StringRegion.
From LeanCageParent Require Import ParentMachine ParentRegion ParentLift.
Import ListNotations.
Open Scope nat_scope.
Lemma parent_source_prepend ge cell P R start next n : P(memory_of start)->store_edge ge start next->
 parent_certificate ge cell P R n next->parent_certificate ge cell P R(S n)start.
Proof.
 intros GOOD EDGE CERT;change(S n)with(1+n).
 eapply parent_bind with(R:=fun endpoint=>endpoint=next).
 - apply parent_from_string;eapply region_source_prepend;[exact GOOD|exact EDGE|].
   apply region_stop;[|reflexivity].
   destruct EDGE as[IN[REAL UNIQUE]].
   (* Store edges may change memory; the tail certificate supplies its invariant. *)
   exact(parent_memory _ _ _ _ _ _ CERT).
 - intros endpoint EQ;subst endpoint;exact CERT.
Qed.
Lemma parent_store_path ge cell P R start count last remaining : store_path ge P start count last->
 parent_certificate ge cell P R remaining last->parent_certificate ge cell P R(count+remaining)start.
Proof.
 intros PATH CERT;induction PATH;cbn;auto;eapply parent_source_prepend;eauto.
Qed.
Lemma parent_choice ge cell P R k m remaining (preferred:Integers.int) : P m->
 (forall value,parent_certificate ge cell P R remaining(Returnstate(Vint value)k m))->
 parent_certificate ge cell P R(S remaining)(Callstate getppid_definition [] k m).
Proof.
 intros GOOD NEXT;eapply parent_next;[exact GOOD| |].
 - exists(parent_observed preferred),(Returnstate(Vint preferred)k m).
   split;[reflexivity|];split;[discriminate|constructor].
 - intros ev target STEP;destruct(getppid_cases _ _ _ _ _ _ STEP)
   as[[value[EV TARGET]]|[[EV TARGET]|[EV TARGET]]];subst.
   + right;right;eexists;split;[reflexivity|];split;[reflexivity|apply NEXT].
   + left;auto.
   + right;left;exists m;auto.
Qed.
