(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-library.source: All executions of finite source control with library waits. *)
From Coq Require Import List Lia Bool.
From compcert Require Import AST Values Memory Events Clight.
Require Import Machine ClightSteps Deterministic StoreSteps Library LibraryMachine LibraryPreservation.
Import ListNotations.

Definition control_wait ev :=
  match ev with library_wait | original_event wait_step => true | _ => false end.
Definition control_progress ev :=
  control_wait ev = false /\ ev <> original_event loss_step /\
  (forall q bytes error, ev <> original_event (partial_loss q bytes error)) /\
  (forall source destination bytes schedule, ev <> memcpy_lost source destination bytes schedule).
Definition control_cost events := length (filter (fun ev => negb (control_wait ev)) events).

(* Each node proves real progress AND classifies every actual extended-machine
   transition. The public routine proof constructs this from independent input
   ownership; the final result is never an assumed input contract. *)
Inductive control_certificate ge cell (P : mem -> Prop) (R : val -> mem -> Prop) : nat -> Clight.state -> Prop :=
| control_return : forall value m,
    P m -> R value m -> control_certificate ge cell P R 0 (Returnstate value Kstop m)
| control_next : forall n s,
    P (memory_of s) ->
    (exists ev target, control_progress ev /\ library_step ge cell (live s) ev target) ->
    (forall ev target, library_step ge cell (live s) ev target ->
      (control_wait ev = true /\ target = live s) \/
      (exists after, target = dead after /\ P after) \/
      (exists next, control_progress ev /\ target = live next /\ control_certificate ge cell P R n next)) ->
    control_certificate ge cell P R (S n) s.

Lemma control_memory : forall ge cell P R n s,
  control_certificate ge cell P R n s -> P (memory_of s).
Proof. intros; inversion H; assumption. Qed.

Lemma control_return_step : forall ge cell value m ev target,
  library_step ge cell (live (Returnstate value Kstop m)) ev target ->
  ev = original_event loss_step /\ target = dead m.
Proof.
  intros ge cell value m ev target STEP.
  destruct (internal_boundary_unchanged ge cell (Returnstate value Kstop m) _ _ I STEP)
    as [old [EV OLD]]. subst. destruct (returned_step _ _ _ _ _ _ OLD); subst; auto.
Qed.

Theorem control_result_exact : forall ge cell P R n value m,
  control_certificate ge cell P R n (Returnstate value Kstop m) -> R value m.
Proof.
  intros ge cell P R n value m CERT. inversion CERT; subst; auto.
  destruct H0 as [ev [target [[_ [NOTLOSS _]] STEP]]].
  destruct (control_return_step _ _ _ _ _ _ STEP) as [EV _]; contradiction.
Qed.

Theorem control_all_prefixes : forall ge cell P R n start,
  control_certificate ge cell P R n start ->
  forall events target, library_steps ge cell (live start) events target ->
    P (routine_memory target) /\ control_cost events <= S n /\
    (forall s, target = live s -> exists remaining, control_certificate ge cell P R remaining s).
Proof.
  intros ge cell P R n start CERT events target RUN.
  remember (live start) as initial eqn:INIT. revert start n INIT CERT.
  induction RUN as [s|s ev mid events target STEP RUN IH]; intros start n INIT CERT; subst s.
  - split; [exact (control_memory ge cell P R n start CERT)|]. split; [cbn; lia|].
    intros s EQ; inversion EQ; subst; eauto.
  - inversion CERT as [value m GOOD RESULT|count s GOOD PROGRESS CASES]; subst.
    + destruct (control_return_step _ _ _ _ _ _ STEP) as [EV TARGET]; subst.
      destruct (library_dead_steps _ _ _ _ _ RUN) as [ES TARGET]; subst.
      cbn [routine_memory control_cost control_wait filter negb length].
      split; [assumption|]. split; [lia|intros; discriminate].
    + destruct (CASES _ _ STEP) as [[WAIT TARGET]|[[after [TARGET PRESERVED]]|
        [next [[ADV _] [TARGET TAIL]]]]]; subst mid.
      * destruct (IH _ _ eq_refl CERT) as [MEM [BOUND LIVE]].
        split; [assumption|]. split; [|exact LIVE].
        unfold control_cost; cbn. rewrite WAIT; exact BOUND.
      * destruct (library_dead_steps _ _ _ _ _ RUN) as [ES TARGET']; subst.
        split; [exact PRESERVED|]. split; [|intros; discriminate].
        unfold control_cost; cbn. destruct (control_wait ev); cbn; lia.
      * destruct (IH _ _ eq_refl TAIL) as [MEM [BOUND LIVE]].
        split; [assumption|]. split; [|exact LIVE].
        unfold control_cost; cbn. rewrite ADV; cbn. unfold control_cost in BOUND; lia.
Qed.

Theorem control_defined_prefix : forall ge cell P R n start events s,
  control_certificate ge cell P R n start ->
  library_steps ge cell (live start) events (live s) ->
  (exists value m, s = Returnstate value Kstop m /\ R value m) \/
  (exists ev target, control_progress ev /\ library_step ge cell (live s) ev target).
Proof.
  intros ge cell P R n start events s CERT RUN.
  destruct (control_all_prefixes _ _ _ _ _ _ CERT _ _ RUN) as [_ [_ LIVE]].
  destruct (LIVE s eq_refl) as [remaining TAIL]. inversion TAIL; subst; eauto.
Qed.

Theorem control_all_returns : forall ge cell P R n start events value m,
  control_certificate ge cell P R n start ->
  library_steps ge cell (live start) events (live (Returnstate value Kstop m)) -> R value m.
Proof.
  intros ge cell P R n start events value m CERT RUN.
  destruct (control_all_prefixes _ _ _ _ _ _ CERT _ _ RUN) as [_ [_ LIVE]].
  destruct (LIVE _ eq_refl) as [remaining TAIL]. eapply control_result_exact; exact TAIL.
Qed.

Lemma control_source_prepend : forall ge cell P R s next n,
  P (memory_of s) -> store_edge ge s next -> control_certificate ge cell P R n next ->
  control_certificate ge cell P R (S n) s.
Proof.
  intros ge cell P R s next n GOOD EDGE CERT. eapply control_next; [exact GOOD| |].
  - exists (original_event (source_step E0)), (live next). split.
    + unfold control_progress; cbn. repeat split; discriminate.
    + constructor. destruct EDGE as [IN [REAL _]]; apply internal; assumption.
  - intros ev target STEP. pose proof EDGE as [IN _].
    destruct (internal_boundary_unchanged _ _ _ _ _ IN STEP) as [old [EV OLD]]; subst.
    destruct (store_edge_cases _ _ _ _ _ _ EDGE OLD) as [[EV TARGET]|[EV TARGET]]; subst.
    + right; right; exists next. split.
      * unfold control_progress; cbn; repeat split; discriminate.
      * auto.
    + right; left. exists (memory_of s); auto.
Qed.

Lemma control_source_path : forall ge cell P R start count last remaining,
  store_path ge P start count last -> control_certificate ge cell P R remaining last ->
  control_certificate ge cell P R (count + remaining) start.
Proof.
  intros ge cell P R start count last remaining PATH CERT; induction PATH; cbn; auto.
  eapply control_source_prepend; eauto.
Qed.

Lemma control_strcmp : forall ge cell P R left right xs ys k m remaining,
  P m -> c_string m left xs -> c_string m right ys ->
  (forall value, strcmp_result m left right value ->
    control_certificate ge cell P R remaining (Returnstate (Vint value) k m)) ->
  control_certificate ge cell P R (S remaining)
    (Callstate strcmp_definition [address_value left; address_value right] k m).
Proof.
  intros ge cell P R left right xs ys k m remaining GOOD LEFT RIGHT RETURN.
  eapply control_next; [exact GOOD| |].
  - destruct (strcmp_progress m left right) as [value RESULT].
    { exists xs, ys; auto. }
    exists (strcmp_returned left right value), (live (Returnstate (Vint value) k m)).
    split; [unfold control_progress; cbn; repeat split; discriminate|constructor; assumption].
  - intros ev target STEP.
    destruct (strcmp_boundary_cases _ _ _ _ _ _ _ _ _ _ LEFT RIGHT STEP)
      as [[value [RESULT [EV TARGET]]]|[[EV TARGET]|[EV TARGET]]]; subst.
    + right; right. exists (Returnstate (Vint value) k m). split.
      * unfold control_progress; cbn; repeat split; discriminate.
      * split; [reflexivity|apply RETURN; exact RESULT].
    + left; auto.
    + right; left; exists m; auto.
Qed.
