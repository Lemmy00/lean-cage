(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-parent.history: Preserve actual observations and ordered source memory. *)
From Stdlib Require Import List Lia Bool.
From compcert Require Import AST Values Memory Events Clight.
Require Import Machine Deterministic.
From LeanCageArguments Require Import StringMachine.
From LeanCageValidation Require Import StringRegion.
From LeanCageParent Require Import ParentMachine.
Import ListNotations.
Open Scope nat_scope.
Inductive parent_certificate ge cell(P:mem->Prop)(R:Clight.state->Prop) : nat->Clight.state->Prop :=
| parent_stop : forall n s,P(memory_of s)->R s->parent_certificate ge cell P R n s
| parent_next : forall n s,P(memory_of s)->
 (exists ev next,parent_waiting ev=false /\ ev<>parent_loss /\ parent_step ge cell(live s)ev(live next))->
 (forall ev target,parent_step ge cell(live s)ev target->
 (parent_waiting ev=true /\ target=live s) \/
 (exists after,target=dead after /\ P after) \/
 (exists next,target=live next /\ parent_waiting ev=false /\ parent_certificate ge cell P R n next))->
 parent_certificate ge cell P R(S n)s.
Lemma parent_memory ge cell P R n s : parent_certificate ge cell P R n s->P(memory_of s).
Proof. intros CERT;inversion CERT;assumption. Qed.
Lemma parent_weaken ge cell P R n s : parent_certificate ge cell P R n s->
 forall larger,n<=larger->parent_certificate ge cell P R larger s.
Proof.
 revert s;induction n as[|n IH];intros s CERT larger BOUND.
 - inversion CERT;subst;constructor;assumption.
 - inversion CERT as[count ss GOOD RESULT|count ss GOOD PROGRESS CASES];subst.
   + constructor;assumption.
   + destruct larger;[lia|];eapply parent_next;[exact GOOD|exact PROGRESS|].
     intros ev target STEP;destruct(CASES _ _ STEP)as[WAIT|[DEAD|[next[TARGET[ADV TAIL]]]]];auto.
     right;right;exists next;split;[exact TARGET|];split;[exact ADV|].
     apply IH with(s:=next);[exact TAIL|lia].
Qed.
Theorem parent_execution_split ge cell P R n start : parent_certificate ge cell P R n start->
 forall events target,parent_steps ge cell(live start)events target->
 (P(routine_memory target) /\ parent_cost events<=S n /\
  (forall s,target=live s->exists remaining,parent_certificate ge cell P R remaining s)) \/
 (exists prefix endpoint rest,events=prefix++rest /\ parent_cost prefix<=n /\
  parent_steps ge cell(live start)prefix(live endpoint) /\ P(memory_of endpoint) /\ R endpoint /\
  parent_steps ge cell(live endpoint)rest target).
Proof.
 intros CERT events target RUN;remember(live start)as initial eqn:INIT.
 revert start n INIT CERT;induction RUN as[initial|initial ev mid events target STEP RUN IH];
 intros start n INIT CERT;subst initial.
 - left;split;[exact(parent_memory ge cell P R n start CERT)|];split;[cbn;lia|].
   intros s EQ;inversion EQ;subst;eauto.
 - inversion CERT as[count s GOOD RESULT|count s GOOD PROGRESS CASES];subst.
   + right;exists [],start,(ev::events);split;[reflexivity|];split;[cbn;lia|];
     split;[constructor|];split;[exact GOOD|];split;[exact RESULT|];econstructor;eassumption.
   + destruct(CASES _ _ STEP)as[[WAIT TARGET]|[[after[TARGET PRESERVED]]|[next[TARGET[ADV TAIL]]]]];subst mid.
     * destruct(IH _ _ eq_refl CERT)as[[MEM[BOUND LIVE]]|[prefix[endpoint[rest[ES[COST[PRE[MEM[RESULT POST]]]]]]]]].
       -- left;split;[exact MEM|];split;[unfold parent_cost;cbn;rewrite WAIT;exact BOUND|exact LIVE].
       -- right;exists(ev::prefix),endpoint,rest;subst events;split;[reflexivity|];split.
          ++ unfold parent_cost;cbn;rewrite WAIT;exact COST.
          ++ split;[econstructor;eassumption|];auto.
     * destruct(parent_dead_steps _ _ _ _ _ RUN)as[ES TARGET];subst.
       left;split;[exact PRESERVED|];split;[unfold parent_cost;cbn;destruct(parent_waiting ev);cbn;lia|intros;discriminate].
     * destruct(IH _ _ eq_refl TAIL)as[[MEM[BOUND LIVE]]|[prefix[endpoint[rest[ES[COST[PRE[MEM[RESULT POST]]]]]]]]].
       -- left;split;[exact MEM|];split;[|exact LIVE].
          unfold parent_cost;cbn;rewrite ADV;cbn;unfold parent_cost in BOUND;lia.
       -- right;exists(ev::prefix),endpoint,rest;subst events;split;[reflexivity|];split.
          ++ unfold parent_cost;cbn;rewrite ADV;cbn;unfold parent_cost in COST;lia.
          ++ split;[econstructor;eassumption|];auto.
Qed.
Theorem parent_live_progress ge cell P R n s : parent_certificate ge cell P R n s->
 R s \/ exists ev next,parent_waiting ev=false /\ ev<>parent_loss /\ parent_step ge cell(live s)ev(live next).
Proof. intros CERT;inversion CERT;subst;auto. Qed.
Lemma parent_bind ge cell P R Q n start extra :
 parent_certificate ge cell P R n start->
 (forall endpoint,R endpoint->parent_certificate ge cell P Q extra endpoint)->
 parent_certificate ge cell P Q(n+extra)start.
Proof.
 revert start;induction n as[|n IH];intros start CERT NEXT;
 inversion CERT as[count s GOOD RESULT|count s GOOD PROGRESS CASES];subst;cbn.
 - apply NEXT;exact RESULT.
 - apply parent_weaken with(n:=extra);[apply NEXT;exact RESULT|lia].
 - eapply parent_next;[exact GOOD|exact PROGRESS|].
   intros ev target STEP;destruct(CASES _ _ STEP)as[WAIT|[DEAD|[next[TARGET[ADV TAIL]]]]];auto.
   right;right;exists next;split;[exact TARGET|];split;[exact ADV|].
   apply IH;assumption.
Qed.
Theorem parent_actual ge cell P R n start : parent_certificate ge cell P R n start->
 exists events endpoint,parent_steps ge cell(live start)events(live endpoint) /\
 parent_cost events<=n /\ P(memory_of endpoint) /\ R endpoint.
Proof.
 revert start;induction n as[|n IH];intros start CERT;
 inversion CERT as[count s GOOD RESULT|count s GOOD PROGRESS CASES];subst.
 - exists [],start;split;[constructor|];auto.
 - exists [],start;split;[constructor|];split;[cbn;lia|auto].
 - destruct PROGRESS as[ev[next[ADV[NOTLOSS STEP]]]].
   destruct(CASES _ _ STEP)as[[WAIT SAME]|[[after[SAME MEM]]|[ss[SAME[ORD TAIL]]]]];try congruence.
   inversion SAME;subst ss;destruct(IH _ TAIL)as[events[endpoint[RUN[COST[MEM END]]]]].
   exists(ev::events),endpoint;split;[econstructor;eassumption|];split;[|auto].
   unfold parent_cost in *;cbn;rewrite ADV;cbn;lia.
Qed.
