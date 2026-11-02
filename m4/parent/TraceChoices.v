(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-parent.cases: Construct executions with a prescribed actual parent observation. *)
From Stdlib Require Import List Lia Classical_Prop.
From compcert Require Import Integers AST Values Memory Clight.
Require Import Machine.
From LeanCageParent Require Import ParentMachine TraceRegion.
Import ListNotations.
Open Scope nat_scope.

Lemma chosen_progress ge cell P R n history start preferred : trace_certificate ge cell P R n history start->
 R history start \/exists ev next,parent_waiting ev=false /\ev<>parent_loss /\
 parent_step ge cell(live start)ev(live next) /\Forall(fun value=>value=preferred)(observation ev).
Proof.
 intros CERT;inversion CERT as[count h s GOOD RESULT|count h s GOOD PROGRESS CASES];subst;[auto|].
 right;destruct(classic(exists k m,start=Callstate getppid_definition [] k m))as[[k[m EQ]]|OTHER].
 - subst start;exists(parent_observed preferred),(Returnstate(Vint preferred)k m).
   split;[reflexivity|];split;[discriminate|];split;[constructor|repeat constructor].
 - destruct PROGRESS as[ev[next[WAIT[NOTLOSS STEP]]]].
   exists ev,next;split;[exact WAIT|];split;[exact NOTLOSS|];split;[exact STEP|].
   destruct ev as[old|value|];cbn[observation];[constructor| |constructor].
   exfalso;inversion STEP;subst;apply OTHER;eexists;eexists;reflexivity.
Qed.

Theorem trace_actual_chosen ge cell P R n history start preferred : trace_certificate ge cell P R n history start->
 exists events endpoint,parent_steps ge cell(live start)events(live endpoint) /\
 parent_cost events<=n /\P(memory_of endpoint) /\R(history++observations events)endpoint /\
 Forall(fun value=>value=preferred)(observations events).
Proof.
 revert history start;induction n as[|n IH];intros history start CERT.
 - inversion CERT;subst;exists [],start;split;[constructor|];split;[cbn;lia|];split;[assumption|].
   split;[cbn;rewrite app_nil_r;assumption|constructor].
 - destruct(chosen_progress _ _ _ _ _ _ _ preferred CERT)as[RESULT|[ev[next[ADV[NOTLOSS[STEP OBS]]]]]].
   + exists [],start;split;[constructor|];split;[cbn;lia|];split;[exact(TraceRegion.trace_memory ge cell P R (S n) history start CERT)|].
     split;[cbn;rewrite app_nil_r;exact RESULT|constructor].
   + inversion CERT as[count h s GOOD END|count h s GOOD PROGRESS CASES];subst.
     * exists [],start;split;[constructor|];split;[cbn;lia|];split;[exact GOOD|].
       split;[cbn;rewrite app_nil_r;exact END|constructor].
     * destruct(CASES _ _ STEP)as[[WAIT[SAME NOOBS]]|[[after[SAME[MEM NOOBS]]]|[ss[SAME[ORD TAIL]]]]];try congruence.
       inversion SAME;subst ss;destruct(IH _ _ TAIL)as[events[endpoint[RUN[COST[MEM[END ALL]]]]]].
       exists(ev::events),endpoint;split;[econstructor;eassumption|];split.
       -- unfold parent_cost in *;cbn;rewrite ADV;cbn;lia.
       -- split;[exact MEM|];split.
          ++ cbn[observations flat_map];rewrite app_assoc;exact END.
          ++ cbn[observations flat_map];apply Forall_app;auto.
Qed.
