(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.encoding: Compose real source paths with owned copy boundaries. *)
From Coq Require Import List.
From compcert Require Import Integers Values Memory Events Clight.
Require Import Machine StoreSteps Library LibraryMachine LibraryPreservation LibraryControl
  CallProgress CallPaths SourceGuarantees CopyControl.
Import ListNotations.

Theorem memcpy_run_cases : forall ge cell m source destination bytes k events target,
  copy_owned m source destination bytes ->
  library_steps ge cell (live (Callstate memcpy_definition (copy_args source destination bytes) k m)) events target ->
  (exists n, events=repeat library_wait n /\
    target=live (Callstate memcpy_definition (copy_args source destination bytes) k m)) \/
  (exists n, events=repeat library_wait n ++ [original_event loss_step] /\ target=dead m) \/
  (exists n schedule after, partial_copy destination bytes m schedule after /\
    events=repeat library_wait n ++ [memcpy_lost source destination bytes schedule] /\ target=dead after) \/
  (exists n after rest, copy_result m source destination bytes after /\
    events=repeat library_wait n ++ memcpy_returned source destination bytes :: rest /\
    library_steps ge cell (live (Returnstate (address_value destination) k after)) rest target).
Proof.
  intros ge cell m source destination bytes k events target OWN RUN.
  remember (live (Callstate memcpy_definition (copy_args source destination bytes) k m)) as initial eqn:INIT.
  induction RUN as [s|s ev mid rest last STEP RUN IH];subst s.
  - left;exists 0%nat;auto.
  - destruct (memcpy_boundary_cases _ _ _ _ _ _ _ _ _ OWN STEP)
      as [[after [RESULT [EV TARGET]]]|[[schedule [after [PART [EV TARGET]]]]|[[EV TARGET]|[EV TARGET]]]];subst.
    + right;right;right;exists 0%nat,after,rest;auto.
    + destruct (library_dead_steps _ _ _ _ _ RUN) as [ES TARGET];subst.
      right;right;left;exists 0%nat,schedule,after;auto.
    + destruct (IH eq_refl)
        as [[n [ES TARGET]]|[[n [ES TARGET]]|[[n [schedule [after [PART [ES TARGET]]]]]|[n [after [tail [RESULT [ES AFTER]]]]]]]];subst.
      * left;exists (S n);auto.
      * right;left;exists (S n);auto.
      * right;right;left;exists (S n),schedule,after;auto.
      * right;right;right;exists (S n),after,tail;auto.
    + destruct (library_dead_steps _ _ _ _ _ RUN) as [ES TARGET];subst.
      right;left;exists 0%nat;auto.
Qed.

Theorem memcpy_continuation_guarantee : forall ge cell m source destination bytes k P R,
  copy_owned m source destination bytes -> P m ->
  (forall schedule after, partial_copy destination bytes m schedule after -> P after) ->
  (forall after, copy_result m source destination bytes after ->
    procedure_guarantee ge cell P R (Returnstate (address_value destination) k after)) ->
  procedure_guarantee ge cell P R (Callstate memcpy_definition (copy_args source destination bytes) k m).
Proof.
  intros ge cell m source destination bytes k P R OWN PM PART RETURN. split.
  - intros events target RUN.
    destruct (memcpy_run_cases _ _ _ _ _ _ _ _ _ OWN RUN)
      as [[n [ES TARGET]]|[[n [ES TARGET]]|[[n [schedule [after [COPY [ES TARGET]]]]]|[n [after [rest [RESULT [ES AFTER]]]]]]]].
    + subst;exact PM.
    + subst;exact PM.
    + subst;eapply PART;exact COPY.
    + exact (proj1 (RETURN after RESULT) _ _ AFTER).
  - intros events current RUN.
    destruct (memcpy_run_cases _ _ _ _ _ _ _ _ _ OWN RUN)
      as [[n [ES TARGET]]|[[n [ES TARGET]]|[[n [schedule [after [COPY [ES TARGET]]]]]|[n [after [rest [RESULT [ES AFTER]]]]]]]].
    + inversion TARGET;subst current. destruct (copy_progress _ _ _ _ OWN) as [after RESULT].
      right;exists (memcpy_returned source destination bytes),(live (Returnstate (address_value destination) k after));split.
      * unfold control_progress;cbn;repeat split;discriminate.
      * apply memcpy_step;exact RESULT.
    + discriminate.
    + discriminate.
    + exact (proj2 (RETURN after RESULT) _ _ AFTER).
Qed.

Inductive copy_reaches ge (P : mem -> Prop) (Q : Clight.state -> Prop) : Clight.state -> Prop :=
| copy_reaches_done : forall s, P (memory_of s) -> Q s -> copy_reaches ge P Q s
| copy_reaches_source : forall s next,
    P (memory_of s) -> store_edge ge s next -> copy_reaches ge P Q next -> copy_reaches ge P Q s
| copy_reaches_call : forall m source destination bytes k,
    P m -> copy_owned m source destination bytes ->
    (forall schedule after, partial_copy destination bytes m schedule after -> P after) ->
    (forall after, copy_result m source destination bytes after ->
      copy_reaches ge P Q (Returnstate (address_value destination) k after)) ->
    copy_reaches ge P Q (Callstate memcpy_definition (copy_args source destination bytes) k m).

Theorem copy_reaches_path : forall ge P Q s count next,
  store_path ge P s count next -> copy_reaches ge P Q next -> copy_reaches ge P Q s.
Proof.
  intros ge P Q s count next PATH;induction PATH;intros REST.
  - exact REST.
  - eapply copy_reaches_source;[exact H|exact H0|apply IHPATH;exact REST].
Qed.

Theorem copy_reaches_guarantee : forall ge cell P Q R s,
  copy_reaches ge P Q s ->
  (forall last, Q last -> procedure_guarantee ge cell P R last) ->
  procedure_guarantee ge cell P R s.
Proof.
  intros ge cell P Q R s PATH;induction PATH;intros LAST.
  - apply LAST;assumption.
  - eapply source_path_guarantee.
    + eapply store_next;[exact H|exact H0|]. constructor.
      clear LAST IHPATH. inversion PATH;assumption.
    + apply IHPATH;exact LAST.
  - eapply memcpy_continuation_guarantee;[exact H0|exact H|exact H1|].
    intros;apply H3;[assumption|exact LAST].
Qed.

Theorem copy_reaches_run : forall ge cell P Q s,
  copy_reaches ge P Q s -> exists events last,
    library_steps ge cell (live s) events (live last) /\ Forall control_progress events /\ Q last.
Proof.
  intros ge cell P Q s PATH;induction PATH.
  - exists [],s;split;[constructor|]. split;[constructor|exact H0].
  - destruct IHPATH as [events [last [RUN [PROGRESS POST]]]].
    exists (original_event (source_step E0)::events),last.
    split;[eapply library_steps_cons;[apply original_step;destruct H0 as [IN [STEP _]];
      exact (Machine.internal ge cell s E0 next IN STEP)|exact RUN]|].
    split;[constructor;[unfold control_progress;cbn;repeat split;discriminate|exact PROGRESS]|exact POST].
  - destruct (copy_progress _ _ _ _ H0) as [after RESULT].
    destruct (H3 _ RESULT) as [events [last [RUN [PROGRESS POST]]]].
    exists (memcpy_returned source destination bytes::events),last.
    split;[econstructor;[apply memcpy_step;exact RESULT|exact RUN]|].
    split;[constructor;[unfold control_progress;cbn;repeat split;discriminate|exact PROGRESS]|exact POST].
Qed.
