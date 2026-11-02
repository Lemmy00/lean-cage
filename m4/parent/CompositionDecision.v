(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-parent.cases: Actual observations decide the first parent rejection. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Integers.
From LeanCageMainNumber Require Import NumberMath.
From LeanCageParent Require Import ParentStructure ParentControl ParentDecision ParentTrace.
Import ListNotations.

Lemma matching_history_decision bytes history preferred : matching_history bytes history->
 Forall(fun value=>value=preferred)history->parent_decision bytes preferred=false.
Proof.
 intros[value[observed[PARSED[RANGE[H SIGNED]]]]] ALL;subst history.
 inversion ALL;subst observed;apply parent_decision_exact;exists value;auto.
Qed.
Lemma rejecting_history_decision bytes history preferred :
 ((parent_guard_bad(decimal_number bytes)=true /\history=[]) \/
  (exists observed,history=[observed] /\parent_guard_bad(decimal_number bytes)=false /\
   Int.eq observed(Int.repr(parent_value(decimal_number bytes)))=false))->
 Forall(fun value=>value=preferred)history->parent_decision bytes preferred=true.
Proof.
 intros[[BAD H]|[observed[H[BAD DIFFERENT]]]] ALL;unfold parent_decision;rewrite BAD;[reflexivity|].
 subst history;inversion ALL;subst observed;rewrite DIFFERENT;reflexivity.
Qed.
