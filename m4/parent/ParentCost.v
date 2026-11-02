(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-parent.history: Count the independently constructed source path, excluding waits. *)
From Stdlib Require Import List Lia.
From compcert Require Import Integers.
From LeanCageParent Require Import ParentMachine ParentRuns TraceRegion.
Import ListNotations.
Open Scope nat_scope.
Lemma parent_cost_append first second : parent_cost(first++second)=parent_cost first+parent_cost second.
Proof. unfold parent_cost;rewrite filter_app,length_app;reflexivity. Qed.
Lemma parent_internal_cost n : parent_cost(repeat parent_internal n)=n.
Proof. induction n;[reflexivity|];change(S(parent_cost(repeat parent_internal n))=S n);congruence. Qed.
Lemma parent_wait_cost n : parent_cost(repeat parent_wait n)=0.
Proof. induction n;[reflexivity|];change(parent_cost(repeat parent_wait n)=0);exact IHn. Qed.
Theorem parent_observation_cost count waits observed suffix :
 parent_cost(repeat parent_internal count++repeat parent_wait waits++parent_observed observed::repeat parent_internal suffix)=count+1+suffix.
Proof.
 rewrite !parent_cost_append,parent_internal_cost,parent_wait_cost.
 change(count+(0+S(parent_cost(repeat parent_internal suffix)))=count+1+suffix).
 rewrite parent_internal_cost;lia.
Qed.

Theorem parent_observation_trace count waits observed suffix tail : observations tail=[]->
 observations((repeat parent_internal count++repeat parent_wait waits++parent_observed observed::repeat parent_internal suffix)++tail)=[observed].
Proof.
 intros TAIL;rewrite !observations_append,TAIL.
 rewrite(observations_repeat_empty parent_internal count eq_refl),(observations_repeat_empty parent_wait waits eq_refl).
 change((observed::observations(repeat parent_internal suffix))++[]=[observed]).
 rewrite(observations_repeat_empty parent_internal suffix eq_refl);reflexivity.
Qed.
