(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-receiver.memory: Universal close histories include errors, waiting and loss without cleanup claims. *)
From Coq Require Import List.
From compcert Require Import Integers Values Memory Clight.
Require Import IO Machine Deterministic ProcessEffects LibraryMachine LibraryPreservation
  LibraryControl CallProgress SourceGuarantees.
Import ListNotations.

Theorem close_boundary_cases : forall ge cell fd k m ev target,
  library_step ge cell(live(Callstate close_definition[Vint fd]k m))ev target ->
  (exists reply after,close_effect cell m reply after /\
    ev=close_returned fd reply /\ target=live(Returnstate(Vint(close_value reply))k after)) \/
  (ev=library_wait /\ target=live(Callstate close_definition[Vint fd]k m)) \/
  (ev=original_event loss_step /\ target=dead m).
Proof.
  intros ge cell fd k m ev target STEP;inversion STEP;subst;try discriminate;auto.
  - match goal with OLD : Machine.step _ _ _ _ _ |- _=>inversion OLD;subst;cbn in * end;
      try contradiction;auto;
      match goal with B : boundary _ _ _ |- _=>inversion B;subst;destruct(operation q);discriminate end.
  - left;eauto 6.
Qed.

Theorem close_run_cases : forall ge cell fd k m events target,
  library_steps ge cell(live(Callstate close_definition[Vint fd]k m))events target ->
  (exists n,events=repeat library_wait n /\ target=live(Callstate close_definition[Vint fd]k m)) \/
  (exists n,events=repeat library_wait n++[original_event loss_step] /\ target=dead m) \/
  (exists n reply after rest,close_effect cell m reply after /\
    events=repeat library_wait n++close_returned fd reply::rest /\
    library_steps ge cell(live(Returnstate(Vint(close_value reply))k after))rest target).
Proof.
  intros ge cell fd k m events target RUN.
  remember(live(Callstate close_definition[Vint fd]k m))as initial eqn:INIT.
  induction RUN as[s|s ev mid rest last STEP RUN IH];subst s.
  - left;exists 0;auto.
  - destruct(close_boundary_cases _ _ _ _ _ _ _ STEP)as[[reply[after[EFFECT[EV TARGET]]]]|[[EV TARGET]|[EV TARGET]]];subst.
    + right;right;exists 0,reply,after,rest;auto.
    + destruct(IH eq_refl)as[[n[ES TARGET]]|[[n[ES TARGET]]|[n[reply[after[tail[EFFECT[ES AFTER]]]]]]]];subst.
      * left;exists(S n);auto.
      * right;left;exists(S n);auto.
      * right;right;exists(S n),reply,after,tail;auto.
    + destruct(library_dead_steps _ _ _ _ _ RUN)as[ES TARGET];subst;right;left;exists 0;auto.
Qed.

Theorem close_continuation_guarantee : forall ge cell fd k m P R,
  tls_ready cell m -> P m ->
  (forall reply after,close_effect cell m reply after ->
    procedure_guarantee ge cell P R(Returnstate(Vint(close_value reply))k after)) ->
  procedure_guarantee ge cell P R(Callstate close_definition[Vint fd]k m).
Proof.
  intros ge cell fd k m P R READY PM RETURN;split.
  - intros events target RUN.
    destruct(close_run_cases _ _ _ _ _ _ _ RUN)as[[n[ES TARGET]]|[[n[ES TARGET]]|[n[reply[after[tail[EFFECT[ES AFTER]]]]]]]].
    + subst;exact PM.
    + subst;exact PM.
    + exact(proj1(RETURN _ _ EFFECT)_ _ AFTER).
  - intros events current RUN.
    destruct(close_run_cases _ _ _ _ _ _ _ RUN)as[[n[ES TARGET]]|[[n[ES TARGET]]|[n[reply[after[tail[EFFECT[ES AFTER]]]]]]]].
    + inversion TARGET;subst current;right.
      exists(close_returned fd(close_ok None)),(live(Returnstate(Vint Int.zero)k m));split.
      * unfold control_progress;cbn;repeat split;discriminate.
      * apply close_step;split;[exact READY|constructor].
    + discriminate.
    + exact(proj2(RETURN _ _ EFFECT)_ _ AFTER).
Qed.
