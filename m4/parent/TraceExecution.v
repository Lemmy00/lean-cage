(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-parent.history: Universal splitting uses observations of the selected actual prefix. *)
From Stdlib Require Import List Lia.
From compcert Require Import Integers AST Values Memory Clight.
Require Import Machine Deterministic.
From LeanCageParent Require Import ParentMachine TraceRegion.
Import ListNotations.
Open Scope nat_scope.

Theorem trace_execution_split ge cell P R n history start : trace_certificate ge cell P R n history start->
 forall events target,parent_steps ge cell(live start)events target->
 (P(routine_memory target) /\parent_cost events<=S n /\
  (forall s,target=live s->exists remaining,
    trace_certificate ge cell P R remaining(history++observations events)s)) \/
 (exists prefix endpoint rest,events=prefix++rest /\parent_cost prefix<=n /\
  parent_steps ge cell(live start)prefix(live endpoint) /\P(memory_of endpoint) /\
  R(history++observations prefix)endpoint /\parent_steps ge cell(live endpoint)rest target).
Proof.
 intros CERT events target RUN;remember(live start)as initial eqn:INIT.
 revert history start n INIT CERT;induction RUN as[initial|initial ev mid events target STEP RUN IH];
 intros history start n INIT CERT;subst initial.
 - inversion CERT as[count h s GOOD RESULT|count h s GOOD PROGRESS CASES];subst.
   + right;exists [],start,[];split;[reflexivity|];split;[cbn;lia|].
     split;[constructor|];split;[exact GOOD|];split;[cbn;rewrite app_nil_r;exact RESULT|constructor].
   + left;split;[exact GOOD|];split;[cbn;lia|].
     intros s EQ;inversion EQ;subst;cbn[observations];rewrite app_nil_r;eauto.
 - inversion CERT as[count h s GOOD RESULT|count h s GOOD PROGRESS CASES];subst.
   + right;exists [],start,(ev::events);split;[reflexivity|];split;[cbn;lia|];
     split;[constructor|];split;[exact GOOD|];split;[cbn;rewrite app_nil_r;exact RESULT|];econstructor;eassumption.
   + destruct(CASES _ _ STEP)as[[WAIT[TARGET OBS]]|[[after[TARGET[PRESERVED OBS]]]|[next[TARGET[ADV TAIL]]]]];subst mid.
     * destruct(IH history _ _ eq_refl CERT)as[[MEM[BOUND LIVE]]|[prefix[endpoint[rest[ES[COST[PRE[MEM[RESULT POST]]]]]]]]].
       -- left;split;[exact MEM|];split;[unfold parent_cost;cbn;rewrite WAIT;exact BOUND|].
          intros s EQ;cbn[observations flat_map];rewrite OBS;cbn;apply LIVE;exact EQ.
       -- right;exists(ev::prefix),endpoint,rest;subst events;split;[reflexivity|];split.
          ++ unfold parent_cost;cbn;rewrite WAIT;exact COST.
          ++ split;[econstructor;eassumption|];split;[exact MEM|];split;[|exact POST].
             cbn[observations flat_map];rewrite OBS;exact RESULT.
     * destruct(parent_dead_steps _ _ _ _ _ RUN)as[ES TARGET];subst.
       left;split;[exact PRESERVED|];split;[unfold parent_cost;cbn;destruct(parent_waiting ev);cbn;lia|intros;discriminate].
     * destruct(IH(history++observation ev) _ _ eq_refl TAIL)as[[MEM[BOUND LIVE]]|[prefix[endpoint[rest[ES[COST[PRE[MEM[RESULT POST]]]]]]]]].
       -- left;split;[exact MEM|];split.
          ++ unfold parent_cost;cbn;rewrite ADV;cbn;unfold parent_cost in BOUND;lia.
          ++ intros s EQ;cbn[observations flat_map];rewrite app_assoc;apply LIVE;exact EQ.
       -- right;exists(ev::prefix),endpoint,rest;subst events;split;[reflexivity|];split.
          ++ unfold parent_cost;cbn;rewrite ADV;cbn;unfold parent_cost in COST;lia.
          ++ split;[econstructor;eassumption|];split;[exact MEM|];split;[|exact POST].
             cbn[observations flat_map];rewrite app_assoc;exact RESULT.
Qed.

Theorem trace_actual ge cell P R n history start : trace_certificate ge cell P R n history start->
 exists events endpoint,parent_steps ge cell(live start)events(live endpoint) /\
 parent_cost events<=n /\P(memory_of endpoint) /\R(history++observations events)endpoint.
Proof.
 revert history start;induction n as[|n IH];intros history start CERT;
 inversion CERT as[count h s GOOD RESULT|count h s GOOD PROGRESS CASES];subst.
 - exists [],start;split;[constructor|];split;[cbn;lia|];split;[exact GOOD|];cbn;rewrite app_nil_r;exact RESULT.
 - exists [],start;split;[constructor|];split;[cbn;lia|];split;[exact GOOD|];cbn;rewrite app_nil_r;exact RESULT.
 - destruct PROGRESS as[ev[next[ADV[NOTLOSS STEP]]]].
   destruct(CASES _ _ STEP)as[[WAIT[SAME OBS]]|[[after[SAME[MEM OBS]]]|[ss[SAME[ORD TAIL]]]]];try congruence.
   inversion SAME;subst ss;destruct(IH _ _ TAIL)as[events[endpoint[RUN[COST[MEM END]]]]].
   exists(ev::events),endpoint;split;[econstructor;eassumption|];split.
   + unfold parent_cost in *;cbn;rewrite ADV;cbn;lia.
   + split;[exact MEM|];cbn[observations flat_map];rewrite app_assoc;exact END.
Qed.

Definition trace_guarantee ge cell P R n start :=
 trace_certificate ge cell P R n [] start /\
 (exists events endpoint,parent_steps ge cell(live start)events(live endpoint) /\
 parent_cost events<=n /\P(memory_of endpoint) /\R(observations events)endpoint) /\
 (forall events target,parent_steps ge cell(live start)events target->
 (P(routine_memory target) /\parent_cost events<=S n /\
  (forall s,target=live s->exists remaining,trace_certificate ge cell P R remaining(observations events)s)) \/
 (exists prefix endpoint rest,events=prefix++rest /\parent_cost prefix<=n /\
  parent_steps ge cell(live start)prefix(live endpoint) /\P(memory_of endpoint) /\
  R(observations prefix)endpoint /\parent_steps ge cell(live endpoint)rest target)).
Theorem trace_guaranteed ge cell P R n start : trace_certificate ge cell P R n [] start->
 trace_guarantee ge cell P R n start.
Proof.
 intros CERT;split;[exact CERT|];split.
 - exact(trace_actual _ _ _ _ _ _ _ CERT).
 - exact(trace_execution_split _ _ _ _ _ _ _ CERT).
Qed.
