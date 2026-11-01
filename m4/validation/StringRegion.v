(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.strings: Actual caller checks, owned bytes and explicit execution boundaries. *)
From Stdlib Require Import List Lia Bool.
From compcert Require Import AST Values Memory Events Clight.
Require Import Machine ClightSteps Deterministic StoreSteps Library LibraryMachine.
From LeanCageArguments Require Import StringMachine StringPath.
Import ListNotations.
Open Scope nat_scope.
Inductive region_certificate ge cell(P:mem->Prop)(R:Clight.state->Prop) : nat->Clight.state->Prop :=
| region_stop : forall n s,P(memory_of s)->R s->region_certificate ge cell P R n s
| region_next : forall n s,P(memory_of s)->
 (exists ev next,string_waiting ev=false /\ ev<>string_loss /\ string_step ge cell(live s)ev(live next))->
 (forall ev target,string_step ge cell(live s)ev target->
 (string_waiting ev=true /\ target=live s) \/
 (exists after,target=dead after /\ P after) \/
 (exists next,target=live next /\ string_waiting ev=false /\ region_certificate ge cell P R n next))->
 region_certificate ge cell P R(S n)s.
Lemma region_memory ge cell P R n s : region_certificate ge cell P R n s->P(memory_of s).
Proof. intros CERT;inversion CERT;assumption. Qed.
Lemma region_weaken ge cell P R n s : region_certificate ge cell P R n s->
 forall larger,n<=larger->region_certificate ge cell P R larger s.
Proof.
 revert s;induction n as[|n IH];intros s CERT larger BOUND.
 - inversion CERT;subst;constructor;assumption.
 - inversion CERT as[count ss GOOD RESULT|count ss GOOD PROGRESS CASES];subst.
   + constructor;assumption.
   + destruct larger;[lia|];eapply region_next;[exact GOOD|exact PROGRESS|].
     intros ev target STEP;destruct(CASES _ _ STEP)as[WAIT|[DEAD|[next[TARGET[ADV TAIL]]]]];auto.
     right;right;exists next;split;[exact TARGET|];split;[exact ADV|].
     apply IH with(s:=next);[exact TAIL|lia].
Qed.
Theorem region_execution_split ge cell P R n start : region_certificate ge cell P R n start->
 forall events target,string_steps ge cell(live start)events target->
 (P(routine_memory target) /\ string_cost events<=S n /\
  (forall s,target=live s->exists remaining,region_certificate ge cell P R remaining s)) \/
 (exists prefix endpoint rest,events=prefix++rest /\ string_cost prefix<=n /\
  string_steps ge cell(live start)prefix(live endpoint) /\ P(memory_of endpoint) /\ R endpoint /\
  string_steps ge cell(live endpoint)rest target).
Proof.
 intros CERT events target RUN;remember(live start)as initial eqn:INIT.
 revert start n INIT CERT;induction RUN as[initial|initial ev mid events target STEP RUN IH];
 intros start n INIT CERT;subst initial.
 - left;split;[exact(region_memory ge cell P R n start CERT)|];split;[cbn;lia|].
   intros s EQ;inversion EQ;subst;eauto.
 - inversion CERT as[count s GOOD RESULT|count s GOOD PROGRESS CASES];subst.
   + right;exists [],start,(ev::events);split;[reflexivity|];split;[cbn;lia|];
     split;[constructor|];split;[exact GOOD|];split;[exact RESULT|];econstructor;eassumption.
   + destruct(CASES _ _ STEP)as[[WAIT TARGET]|[[after[TARGET PRESERVED]]|[next[TARGET[ADV TAIL]]]]];subst mid.
     * destruct(IH _ _ eq_refl CERT)as[[MEM[BOUND LIVE]]|[prefix[endpoint[rest[ES[COST[PRE[MEM[RESULT POST]]]]]]]]].
       -- left;split;[exact MEM|];split;[unfold string_cost;cbn;rewrite WAIT;exact BOUND|exact LIVE].
       -- right;exists(ev::prefix),endpoint,rest;subst events;split;[reflexivity|];split.
          ++ unfold string_cost;cbn;rewrite WAIT;exact COST.
          ++ split;[econstructor;eassumption|];auto.
     * destruct(string_dead_steps _ _ _ _ _ RUN)as[ES TARGET];subst.
       left;split;[exact PRESERVED|];split;[unfold string_cost;cbn;destruct(string_waiting ev);cbn;lia|intros;discriminate].
     * destruct(IH _ _ eq_refl TAIL)as[[MEM[BOUND LIVE]]|[prefix[endpoint[rest[ES[COST[PRE[MEM[RESULT POST]]]]]]]]].
       -- left;split;[exact MEM|];split;[|exact LIVE].
          unfold string_cost;cbn;rewrite ADV;cbn;unfold string_cost in BOUND;lia.
       -- right;exists(ev::prefix),endpoint,rest;subst events;split;[reflexivity|];split.
          ++ unfold string_cost;cbn;rewrite ADV;cbn;unfold string_cost in COST;lia.
          ++ split;[econstructor;eassumption|];auto.
Qed.
Theorem region_live_progress ge cell P R n s : region_certificate ge cell P R n s->
 R s \/ exists ev next,string_waiting ev=false /\ ev<>string_loss /\ string_step ge cell(live s)ev(live next).
Proof. intros CERT;inversion CERT;subst;auto. Qed.
Lemma region_source_prepend ge cell P R s next n : P(memory_of s)->store_edge ge s next->
 region_certificate ge cell P R n next->region_certificate ge cell P R(S n)s.
Proof.
 intros GOOD EDGE CERT;eapply region_next;[exact GOOD| |].
 - exists string_source,next;split;[reflexivity|];split;[discriminate|].
   constructor;constructor;destruct EDGE as[IN[REAL UNIQUE]];apply internal;assumption.
 - intros ev target STEP;pose proof EDGE as[IN _].
   destruct(string_internal_exact _ _ _ _ _ IN STEP)as[old[EV OLD]];subst.
   destruct(store_edge_cases _ _ _ _ _ _ EDGE OLD)as[[EV TARGET]|[EV TARGET]];subst.
   + right;right;exists next;auto.
   + right;left;exists(memory_of s);auto.
Qed.
Lemma region_store_path ge cell P R start count last remaining : store_path ge P start count last->
 region_certificate ge cell P R remaining last->region_certificate ge cell P R(count+remaining)start.
Proof.
 intros PATH CERT;induction PATH;cbn;auto;eapply region_source_prepend;eauto.
Qed.
Lemma region_string_path ge cell P R start count last remaining : string_path ge cell start count last->
 P(memory_of start)->region_certificate ge cell P R remaining last->region_certificate ge cell P R(count+remaining)start.
Proof.
 intros PATH;induction PATH;intros GOOD CERT;cbn;auto.
 destruct H as[WAIT[NOTLOSS[REAL[MEM CASES]]]].
 eapply region_next;[exact GOOD|eauto|].
 intros ev' target STEP;destruct(CASES _ _ STEP)as[[EV TARGET]|[[W TARGET]|[EV TARGET]]];subst.
 - right;right;exists next;split;[reflexivity|];split;[exact WAIT|].
   apply IHPATH;[rewrite MEM;exact GOOD|exact CERT].
 - left;auto.
 - right;left;exists(memory_of s);auto.
Qed.
Lemma string_strcmp_cases ge cell left right xs ys k m ev target :
 c_string m left xs->c_string m right ys->
 string_step ge cell(live(Callstate strcmp_definition[address_value left;address_value right]k m))ev target->
 (exists value,strcmp_result m left right value /\ ev=previous_event(strcmp_returned left right value) /\
 target=live(Returnstate(Vint value)k m)) \/
 (ev=previous_event library_wait /\ target=live(Callstate strcmp_definition[address_value left;address_value right]k m)) \/
 (ev=string_loss /\ target=dead m).
Proof.
 intros LEFT RIGHT STEP;inversion STEP;subst.
 destruct(strcmp_boundary_cases _ _ _ _ _ _ _ _ _ _ LEFT RIGHT H)as
 [[value[RESULT[EV TARGET]]]|[[EV TARGET]|[EV TARGET]]];subst;eauto.
Qed.
Lemma region_strcmp ge cell P R left right xs ys k m remaining :
 P m->c_string m left xs->c_string m right ys->
 (forall value,strcmp_result m left right value->region_certificate ge cell P R remaining(Returnstate(Vint value)k m))->
 region_certificate ge cell P R(S remaining)(Callstate strcmp_definition[address_value left;address_value right]k m).
Proof.
 intros GOOD LEFT RIGHT RETURN;eapply region_next;[exact GOOD| |].
 - destruct(strcmp_progress m left right)as[value RESULT];[exists xs,ys;auto|].
   exists(previous_event(strcmp_returned left right value)),(Returnstate(Vint value)k m).
   split;[reflexivity|];split;[discriminate|constructor;constructor;exact RESULT].
 - intros ev target STEP;destruct(string_strcmp_cases _ _ _ _ _ _ _ _ _ _ LEFT RIGHT STEP)
   as[[value[RESULT[EV TARGET]]]|[[EV TARGET]|[EV TARGET]]];subst.
   + right;right;exists(Returnstate(Vint value)k m);split;[reflexivity|];split;[reflexivity|apply RETURN;exact RESULT].
   + left;auto.
   + right;left;exists m;auto.
Qed.
Lemma region_bind ge cell P R Q n start extra :
 region_certificate ge cell P R n start->
 (forall endpoint,R endpoint->region_certificate ge cell P Q extra endpoint)->
 region_certificate ge cell P Q(n+extra)start.
Proof.
 revert start;induction n as[|n IH];intros start CERT NEXT;
 inversion CERT as[count s GOOD RESULT|count s GOOD PROGRESS CASES];subst;cbn.
 - apply NEXT;exact RESULT.
 - apply region_weaken with(n:=extra);[apply NEXT;exact RESULT|lia].
 - eapply region_next;[exact GOOD|exact PROGRESS|].
   intros ev target STEP;destruct(CASES _ _ STEP)as[WAIT|[DEAD|[next[TARGET[ADV TAIL]]]]];auto.
   right;right;exists next;split;[exact TARGET|];split;[exact ADV|].
   apply IH;assumption.
Qed.
Theorem region_actual ge cell P R n start : region_certificate ge cell P R n start->
 exists events endpoint,string_steps ge cell(live start)events(live endpoint) /\
 string_cost events<=n /\ P(memory_of endpoint) /\ R endpoint.
Proof.
 revert start;induction n as[|n IH];intros start CERT;
 inversion CERT as[count s GOOD RESULT|count s GOOD PROGRESS CASES];subst.
 - exists [],start;split;[constructor|];auto.
 - exists [],start;split;[constructor|];split;[cbn;lia|auto].
 - destruct PROGRESS as[ev[next[ADV[NOTLOSS STEP]]]].
   destruct(CASES _ _ STEP)as[[WAIT SAME]|[[after[SAME MEM]]|[ss[SAME[ORD TAIL]]]]];try congruence.
   inversion SAME;subst ss;destruct(IH _ TAIL)as[events[endpoint[RUN[COST[MEM END]]]]].
   exists(ev::events),endpoint;split;[econstructor;eassumption|];split;[|auto].
   unfold string_cost in *;cbn;rewrite ADV;cbn;lia.
Qed.
