(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-parent.history: Preserve actual observations and ordered source memory. *)
From Stdlib Require Import List Lia Bool.
From compcert Require Import AST Values Memory Events Clight.
Require Import Machine.
From LeanCageArguments Require Import StringMachine.
From LeanCageValidation Require Import StringRegion.
From LeanCageParent Require Import ParentMachine ParentRegion.
Import ListNotations.
Open Scope nat_scope.
Theorem parent_from_string ge cell P R n start :
 region_certificate ge cell P R n start->parent_certificate ge cell P R n start.
Proof.
 revert start;induction n as[|n IH];intros start CERT;
 inversion CERT as[count s GOOD RESULT|count s GOOD PROGRESS CASES];subst.
 - apply parent_stop;assumption.
 - apply parent_stop;assumption.
 - eapply parent_next;[exact GOOD| |].
   + destruct PROGRESS as[ev[next[WAIT[NOTLOSS REAL]]]].
     exists(previous ev),next;split;[exact WAIT|];split;[unfold parent_loss;congruence|constructor;exact REAL].
   + intros ev target STEP;inversion STEP;subst.
     * destruct(CASES _ _ H)as[[WAIT TARGET]|[[after[TARGET MEM]]|[next[TARGET[ADV TAIL]]]]].
       -- left;split;assumption.
       -- right;left;exists after;auto.
       -- right;right;exists next;split;[exact TARGET|];split;[exact ADV|apply IH;exact TAIL].
     * destruct PROGRESS as[prior[next[WAIT[NOTLOSS REAL]]]].
       destruct(getppid_old_only_loss _ _ _ _ _ _ REAL)as[EV TARGET];contradiction.
     * destruct PROGRESS as[prior[next[WAIT[NOTLOSS REAL]]]].
       destruct(getppid_old_only_loss _ _ _ _ _ _ REAL)as[EV TARGET];contradiction.
Qed.
Lemma parent_convert ge cell P R n start : parent_certificate ge cell P R n start->
 forall Q S,(forall m,P m->Q m)->(forall s,R s->S s)->parent_certificate ge cell Q S n start.
Proof.
 revert start;induction n as[|n IH];intros start CERT Q S MEMORY END;
 inversion CERT as[count s GOOD RESULT|count s GOOD PROGRESS CASES];subst.
 - constructor;auto.
 - constructor;auto.
 - eapply parent_next;[auto|exact PROGRESS|].
   intros ev target STEP;destruct(CASES _ _ STEP)as[WAIT|[[after[TARGET MEM]]|[next[TARGET[ADV TAIL]]]]];[left;exact WAIT| |].
   + right;left;exists after;auto.
   + right;right;exists next;split;[exact TARGET|];split;[exact ADV|];eapply IH;eauto.
Qed.
