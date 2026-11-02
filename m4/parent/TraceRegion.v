(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-parent.history: The endpoint is indexed by observations of this execution. *)
From Stdlib Require Import List Lia Bool.
From compcert Require Import Integers AST Values Memory Clight.
Require Import Machine StoreSteps.
From LeanCageArguments Require Import StringMachine.
From LeanCageValidation Require Import StringRegion.
From LeanCageParent Require Import ParentMachine.
Import ListNotations.
Open Scope nat_scope.

Definition observation ev : list int := match ev with parent_observed value=>[value]|_=>[] end.
Definition observations events := flat_map observation events.
Lemma observations_append first rest : observations(first++rest)=observations first++observations rest.
Proof. apply flat_map_app. Qed.
Lemma observations_repeat_empty ev n : observation ev=[]->observations(repeat ev n)=[].
Proof. intros EMPTY;induction n;[reflexivity|];cbn[observations repeat flat_map];rewrite EMPTY;exact IHn. Qed.
Inductive trace_certificate ge cell (P:mem->Prop) (R:list int->Clight.state->Prop) :
 nat->list int->Clight.state->Prop :=
| trace_stop : forall n history s,P(memory_of s)->R history s->trace_certificate ge cell P R n history s
| trace_next : forall n history s,P(memory_of s)->
 (exists ev next,parent_waiting ev=false /\ev<>parent_loss /\parent_step ge cell(live s)ev(live next))->
 (forall ev target,parent_step ge cell(live s)ev target->
 (parent_waiting ev=true /\target=live s /\observation ev=[]) \/
 (exists after,target=dead after /\P after /\observation ev=[]) \/
 (exists next,target=live next /\parent_waiting ev=false /\
 trace_certificate ge cell P R n (history++observation ev) next))->
 trace_certificate ge cell P R (S n) history s.

Lemma trace_memory ge cell P R n history s : trace_certificate ge cell P R n history s->P(memory_of s).
Proof. intros CERT;inversion CERT;assumption. Qed.
Lemma trace_weaken ge cell P R n history s : trace_certificate ge cell P R n history s->
 forall larger,n<=larger->trace_certificate ge cell P R larger history s.
Proof.
 revert history s;induction n as[|n IH];intros history s CERT larger BOUND;
 inversion CERT as[count h ss GOOD RESULT|count h ss GOOD PROGRESS CASES];subst.
 - constructor;assumption.
 - constructor;assumption.
 - destruct larger;[lia|];eapply trace_next;[exact GOOD|exact PROGRESS|].
   intros ev target STEP;destruct(CASES _ _ STEP)as[WAIT|[DEAD|[next[TARGET[ADV TAIL]]]]];auto.
   right;right;exists next;split;[exact TARGET|];split;[exact ADV|];eapply IH;eauto;lia.
Qed.
Lemma trace_convert ge cell P R n history start : trace_certificate ge cell P R n history start->
 forall Q S,(forall m,P m->Q m)->(forall h s,R h s->S h s)->trace_certificate ge cell Q S n history start.
Proof.
 revert history start;induction n as[|n IH];intros history start CERT Q S MEMORY END;
 inversion CERT as[count h ss GOOD RESULT|count h ss GOOD PROGRESS CASES];subst.
 - constructor;auto.
 - constructor;auto.
 - eapply trace_next;[auto|exact PROGRESS|].
   intros ev target STEP;destruct(CASES _ _ STEP)as[WAIT|[[after[TARGET[MEM OBS]]]|[next[TARGET[ADV TAIL]]]]];[left;exact WAIT| |].
   + right;left;exists after;auto.
   + right;right;exists next;split;[exact TARGET|];split;[exact ADV|];eapply IH;eauto.
Qed.
Lemma trace_bind ge cell P R Q n history start extra : trace_certificate ge cell P R n history start->
 (forall h endpoint,R h endpoint->trace_certificate ge cell P Q extra h endpoint)->
 trace_certificate ge cell P Q(n+extra)history start.
Proof.
 revert history start;induction n as[|n IH];intros history start CERT NEXT;
 inversion CERT as[count h ss GOOD RESULT|count h ss GOOD PROGRESS CASES];subst;cbn.
 - apply NEXT;exact RESULT.
 - apply trace_weaken with(n:=extra);[apply NEXT;exact RESULT|lia].
 - eapply trace_next;[exact GOOD|exact PROGRESS|].
   intros ev target STEP;destruct(CASES _ _ STEP)as[WAIT|[DEAD|[next[TARGET[ADV TAIL]]]]];auto.
   right;right;exists next;split;[exact TARGET|];split;[exact ADV|];eapply IH;eauto.
Qed.

Theorem trace_from_string ge cell P R n start history :
 region_certificate ge cell P R n start->
 trace_certificate ge cell P(fun h s=>h=history /\R s)n history start.
Proof.
 revert history start;induction n as[|n IH];intros history start CERT;
 inversion CERT as[count s GOOD RESULT|count s GOOD PROGRESS CASES];subst.
 - apply trace_stop;auto.
 - apply trace_stop;auto.
 - eapply trace_next;[exact GOOD| |].
   + destruct PROGRESS as[ev[next[WAIT[NOTLOSS REAL]]]].
     exists(previous ev),next;split;[exact WAIT|];split;[unfold parent_loss;congruence|constructor;exact REAL].
   + intros ev target STEP;inversion STEP;subst.
     * destruct(CASES _ _ H)as[[WAIT TARGET]|[[after[TARGET MEM]]|[next[TARGET[ADV TAIL]]]]].
       -- left;auto.
       -- right;left;exists after;auto.
       -- right;right;exists next;split;[exact TARGET|];split;[exact ADV|].
          cbn[observation];rewrite app_nil_r;apply IH;exact TAIL.
     * destruct PROGRESS as[prior[next[WAIT[NOTLOSS REAL]]]].
       destruct(getppid_old_only_loss _ _ _ _ _ _ REAL)as[EV TARGET];contradiction.
     * destruct PROGRESS as[prior[next[WAIT[NOTLOSS REAL]]]].
       destruct(getppid_old_only_loss _ _ _ _ _ _ REAL)as[EV TARGET];contradiction.
Qed.
Lemma trace_store_path ge cell P R start count last remaining history : store_path ge P start count last->
 trace_certificate ge cell P R remaining history last->trace_certificate ge cell P R(count+remaining)history start.
Proof.
 intros PATH CERT;eapply trace_bind with(R:=fun h s=>h=history /\s=last).
 - apply trace_from_string;replace count with(count+0)at 1 by lia.
   eapply region_store_path;[exact PATH|];apply region_stop;[eapply trace_memory;exact CERT|reflexivity].
 - intros h endpoint[EQ LAST];subst;exact CERT.
Qed.
Lemma trace_choice ge cell P R k m remaining history (preferred:int) : P m->
 (forall value,trace_certificate ge cell P R remaining(history++[value])(Returnstate(Vint value)k m))->
 trace_certificate ge cell P R(S remaining)history(Callstate getppid_definition [] k m).
Proof.
 intros GOOD NEXT;eapply trace_next;[exact GOOD| |].
 - exists(parent_observed preferred),(Returnstate(Vint preferred)k m).
   split;[reflexivity|];split;[discriminate|constructor].
 - intros ev target STEP;destruct(getppid_cases _ _ _ _ _ _ STEP)
   as[[value[EV TARGET]]|[[EV TARGET]|[EV TARGET]]];subst.
   + right;right;eexists;split;[reflexivity|];split;[reflexivity|apply NEXT].
   + left;auto.
   + right;left;exists m;auto.
Qed.
