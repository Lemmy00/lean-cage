(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.main-inputs: All actual prefixes before the explicit source boundary. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Clight.
Require Import Machine Deterministic StoreSteps ScalarMemory.
From LeanCageMain Require Import MainMemory.
Import ListNotations.
Open Scope Z_scope.
Theorem store_path_bounded_prefix ge cell P start count last events target :
 store_path ge P start count last -> steps ge cell(live start)events target ->
 (length events<=count)%nat ->
 (exists s rest,target=live s /\ store_path ge P s rest last /\ (length events+rest=count)%nat) \/
 (exists m,target=dead m /\ P m).
Proof.
 intros SCRIPT RUN;remember(live start)as initial eqn:INIT.
 revert start count INIT SCRIPT;induction RUN as [initial|initial ev mid events target STEP RUN IH];
 intros start count INIT SCRIPT BOUND;subst initial.
 - left;exists start,count;cbn;auto.
 - inversion SCRIPT as [s GOOD|s next n final GOOD EDGE TAIL];subst;[cbn in BOUND;lia|].
   destruct(store_edge_cases _ _ _ _ _ _ EDGE STEP)as[[EV TARGET]|[EV TARGET]];subst.
   + destruct(IH _ _ eq_refl TAIL ltac:(cbn in BOUND;lia))as
      [[s [rest [TARGET [PATH LEN]]]]|[m [TARGET GOOD']]].
     * left;exists s,rest;cbn;auto.
     * right;exists m;auto.
   + destruct(dead_steps _ _ _ _ _ RUN)as[ES TARGET];subst;right;eexists;auto.
Qed.
Theorem store_path_bounded_memory ge cell P start count last events target :
 store_path ge P start count last -> steps ge cell(live start)events target ->
 (length events<=count)%nat -> P(routine_memory target).
Proof.
 intros SCRIPT RUN BOUND;destruct(store_path_bounded_prefix _ _ _ _ _ _ _ _ SCRIPT RUN BOUND)
 as[[s [rest [TARGET [PATH LEN]]]]|[m [TARGET GOOD]]];subst;cbn;[eapply store_path_initial;eassumption|assumption].
Qed.
Theorem store_path_bounded_progress ge cell P start count last events s :
 store_path ge P start count last -> steps ge cell(live start)events(live s) ->
 (length events<count)%nat -> exists next,step ge cell(live s)(source_step E0)(live next).
Proof.
 intros SCRIPT RUN BOUND;destruct(store_path_bounded_prefix _ _ _ _ _ _ _ _ SCRIPT RUN ltac:(lia))
 as[[ss [rest [TARGET [PATH LEN]]]]|[m [TARGET GOOD]]];[|discriminate].
 inversion TARGET;subst ss;inversion PATH;subst;[lia|].
 destruct H0 as[IN[REAL UNIQUE]];exists next;apply internal;assumption.
Qed.
Theorem store_path_bounded_endpoint ge cell P start count last events s :
 store_path ge P start count last -> steps ge cell(live start)events(live s) ->
 length events=count -> s=last.
Proof.
 intros SCRIPT RUN LEN;destruct(store_path_bounded_prefix _ _ _ _ _ _ _ _ SCRIPT RUN ltac:(lia))
 as[[ss [rest [TARGET [PATH SIZE]]]]|[m [TARGET GOOD]]];[|discriminate].
 inversion TARGET;subst ss;assert(rest=0%nat)by lia;subst;inversion PATH;reflexivity.
Qed.
Lemma policy_cells_valid i values : 0<=i -> i+Z.of_nat(length values)<=10 ->
 Forall(scalar_valid 80)(policy_cells i values).
Proof.
 revert i;induction values as[|v rest IH];intros i LOW HIGH;[constructor|].
 constructor.
 - change(0<=8*i /\ 8*i+8<=80 /\ (8|8*i));split;[lia|]. split;[change(i+Z.of_nat(S(length rest))<=10)in HIGH;lia|exists i;ring].
 - apply IH;cbn in HIGH;lia.
Qed.
Lemma policy_cells_lower i values : Forall(fun c=>8*i<=scalar_offset c)(policy_cells i values).
Proof.
 revert i;induction values as[|v rest IH];intros i;[constructor|].
 constructor;[change(8*i<=8*i);lia|]. eapply Forall_impl with(P:=fun c=>8*(i+1)<=scalar_offset c);[intros c BOUND;lia|exact(IH(i+1))].
Qed.
Lemma policy_cells_ordered i values : scalar_orderedb(policy_cells i values)=true.
Proof.
 revert i;induction values as[|v rest IH];intros i;[reflexivity|].
 cbn[policy_cells scalar_orderedb];apply Bool.andb_true_iff;split;[|apply IH].
 apply forallb_forall;intros c IN;apply Z.leb_le.
 pose proof(policy_cells_lower(i+1)rest)as LOWER;rewrite Forall_forall in LOWER;specialize(LOWER c IN);change(8*i+8<=scalar_offset c);lia.
Qed.
Theorem policy_stores_outside policy i before values after :
 0<=i -> i+Z.of_nat(length values)<=10 -> policy_stores policy i before values after ->
 Mem.unchanged_on(fun b pos=>b<>policy \/ pos<0 \/ 80<=pos)before after.
Proof.
 intros LOW HIGH STORES;eapply scalar_stores_outside;[exact STORES|apply policy_cells_valid;assumption].
Qed.
Theorem policy_stores_values policy i before values after cell :
 policy_stores policy i before values after -> In cell(policy_cells i values) ->
 Mem.load(scalar_chunk cell)after policy(scalar_offset cell)=Some(Val.load_result(scalar_chunk cell)(scalar_value cell)).
Proof.
 intros STORES IN;eapply scalar_stores_fields;[exact STORES|apply scalar_orderedb_sound;apply policy_cells_ordered|exact IN].
Qed.
Theorem policy_prefix_outside policy i before values after :
 0<=i -> i+Z.of_nat(length values)<=10 -> policy_prefix policy i before values after ->
 Mem.unchanged_on(fun b pos=>b<>policy \/ pos<0 \/ 80<=pos)before after.
Proof.
 intros LOW HIGH[done[rest[EQ STORES]]];eapply policy_stores_outside;[exact LOW| |exact STORES].
 rewrite EQ,length_app in HIGH;lia.
Qed.
