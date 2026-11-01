(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-controller.digest: Whole-function certificates cover every actual execution. *)
From Stdlib Require Import List Lia Bool.
From compcert Require Import AST Values Memory Events Clight.
Require Import Machine ClightSteps Deterministic LibraryMachine.
From LeanCageArguments Require Import StringMachine StringPath.
Import ListNotations.
Inductive string_certificate ge cell(P:mem->Prop)(R:val->mem->Prop) : nat->Clight.state->Prop :=
| string_return : forall n v m,P m->R v m->
 string_certificate ge cell P R n(Returnstate v Kstop m)
| string_advance : forall n s,P(memory_of s)->
 (exists ev next,string_waiting ev=false /\ ev<>string_loss /\ string_step ge cell(live s)ev(live next))->
 (forall ev target,string_step ge cell(live s)ev target->
 (string_waiting ev=true /\ target=live s) \/
 (exists after,target=dead after /\ P after) \/
 (exists next,target=live next /\ string_waiting ev=false /\ string_certificate ge cell P R n next))->
 string_certificate ge cell P R(S n)s.
Lemma string_certificate_memory ge cell P R n s :
 string_certificate ge cell P R n s->P(memory_of s).
Proof. intros CERT;inversion CERT;assumption. Qed.
Lemma string_return_only_loss ge cell value m ev target :
 string_step ge cell(live(Returnstate value Kstop m))ev target->
 ev=string_loss /\ target=dead m.
Proof.
 intros STEP;destruct(string_internal_exact ge cell (Returnstate value Kstop m) ev target I STEP)as[old[EV OLD]];subst.
 destruct(returned_step _ _ _ _ _ _ OLD);subst;auto.
Qed.
Lemma string_certificate_result ge cell P R n value m :
 string_certificate ge cell P R n(Returnstate value Kstop m)->R value m.
Proof.
 intros CERT;inversion CERT;subst;auto.
 destruct H0 as[ev[next[WAIT[NOTLOSS STEP]]]].
 destruct(string_return_only_loss _ _ _ _ _ _ STEP);discriminate.
Qed.
Theorem string_certificate_all_prefixes ge cell P R n start :
 string_certificate ge cell P R n start->forall events target,
 string_steps ge cell(live start)events target->
 P(routine_memory target) /\ string_cost events<=S n /\
 (forall s,target=live s->exists remaining,string_certificate ge cell P R remaining s).
Proof.
 intros CERT events target RUN;remember(live start)as initial eqn:INIT.
 revert start n INIT CERT;induction RUN as[initial|initial ev mid events target STEP RUN IH];
 intros start n INIT CERT;subst initial.
 - split;[exact(string_certificate_memory ge cell P R n start CERT)|];split;[cbn;lia|].
   intros s EQ;inversion EQ;subst;eauto.
 - inversion CERT as[count v m GOOD RESULT|count s GOOD PROGRESS CASES];subst.
   + destruct(string_return_only_loss _ _ _ _ _ _ STEP)as[EV TARGET];subst.
     destruct(string_dead_steps _ _ _ _ _ RUN)as[ES TARGET];subst.
     split;[exact GOOD|];split;[cbn;lia|intros;discriminate].
   + destruct(CASES _ _ STEP)as[[WAIT TARGET]|[[after[TARGET PRESERVED]]|
     [next[TARGET[ADV TAIL]]]]];subst mid.
     * destruct(IH _ _ eq_refl CERT)as[MEM[BOUND LIVE]].
       split;[exact MEM|];split;[|exact LIVE].
       unfold string_cost;cbn;rewrite WAIT;exact BOUND.
     * destruct(string_dead_steps _ _ _ _ _ RUN)as[ES TARGET];subst.
       split;[exact PRESERVED|];split;[|intros;discriminate].
       unfold string_cost;cbn;destruct(string_waiting ev);cbn;lia.
     * destruct(IH _ _ eq_refl TAIL)as[MEM[BOUND LIVE]].
       split;[exact MEM|];split;[|exact LIVE].
       unfold string_cost;cbn;rewrite ADV;cbn;unfold string_cost in BOUND;lia.
Qed.
Theorem string_certificate_defined ge cell P R n start events s :
 string_certificate ge cell P R n start->string_steps ge cell(live start)events(live s)->
 (exists v m,s=Returnstate v Kstop m /\ R v m) \/
 (exists ev next,string_waiting ev=false /\ ev<>string_loss /\ string_step ge cell(live s)ev(live next)).
Proof.
 intros CERT RUN;destruct(string_certificate_all_prefixes _ _ _ _ _ _ CERT _ _ RUN)as[_[_ LIVE]].
 destruct(LIVE s eq_refl)as[remaining TAIL];inversion TAIL;subst;eauto.
Qed.
Theorem string_certificate_all_returns ge cell P R n start events v m :
 string_certificate ge cell P R n start->
 string_steps ge cell(live start)events(live(Returnstate v Kstop m))->R v m.
Proof.
 intros CERT RUN;destruct(string_certificate_all_prefixes _ _ _ _ _ _ CERT _ _ RUN)as[_[_ LIVE]].
 destruct(LIVE _ eq_refl)as[remaining TAIL];eapply string_certificate_result;exact TAIL.
Qed.
Lemma string_path_certificate ge cell P R start count last remaining :
 string_path ge cell start count last->P(memory_of start)->
 string_certificate ge cell P R remaining last->string_certificate ge cell P R(count+remaining)start.
Proof.
 intros PATH;induction PATH;intros GOOD CERT;cbn;auto.
 destruct H as[WAIT[NOTLOSS[REAL[MEM CASES]]]].
 eapply string_advance;[exact GOOD|eauto|].
 intros ev' target STEP;destruct(CASES _ _ STEP)as[[EV TARGET]|[[W TARGET]|[EV TARGET]]];subst.
 - right;right;exists next;split;[reflexivity|];split;[exact WAIT|].
   apply IHPATH;[rewrite MEM;exact GOOD|exact CERT].
 - left;auto.
 - right;left;exists(memory_of s);auto.
Qed.
Lemma string_certificate_weaken ge cell P R n s : string_certificate ge cell P R n s->
 forall larger,n<=larger->string_certificate ge cell P R larger s.
Proof.
 revert s;induction n as[|n IH];intros s CERT larger BOUND.
 - inversion CERT;subst;constructor;assumption.
 - inversion CERT as[count v m GOOD RESULT|count ss GOOD PROGRESS CASES];subst.
   + constructor;assumption.
   + destruct larger;[lia|];eapply string_advance;[exact GOOD|exact PROGRESS|].
     intros ev target STEP;destruct(CASES _ _ STEP)as[WAIT|[DEAD|[next[TARGET[ADV TAIL]]]]];auto.
     right;right;exists next;split;[exact TARGET|];split;[exact ADV|].
     apply IH with(s:=next);[exact TAIL|lia].
Qed.
