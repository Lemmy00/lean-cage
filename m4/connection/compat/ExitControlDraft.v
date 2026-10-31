(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-callers.control: Every local exit history retains waits and terminal loss. *)
From Coq Require Import List.
From compcert Require Import Integers Values Memory Clight.
Require Import Machine LibraryMachine LibraryPreservation.
Import ListNotations.

Theorem exit_histories : forall ge cell code k m events target,
  library_steps ge cell (live (Callstate exit_definition [Vint code] k m)) events target ->
  (exists n, events = repeat library_wait n /\
    target = live (Callstate exit_definition [Vint code] k m)) \/
  (exists n, events = repeat library_wait n ++ [exit_requested code] /\ target = dead m) \/
  (exists n, events = repeat library_wait n ++ [original_event loss_step] /\ target = dead m).
Proof.
  intros ge cell code k m events; induction events as [|ev events IH]; intros target RUN.
  - inversion RUN; subst; left; exists 0%nat; auto.
  - inversion RUN; subst.
    match goal with STEP : library_step _ _ _ _ _ |- _ =>
      destruct (exit_never_returns _ _ _ _ _ _ _ STEP) as [[EV TARGET]|[[EV TARGET]|[EV TARGET]]] end; subst.
    + match goal with TAIL : library_steps _ _ _ events target |- _ =>
        destruct (IH _ TAIL) as [[n [ES EQ]]|[[n [ES EQ]]|[n [ES EQ]]]] end; subst.
      * left; exists (S n); auto.
      * right; left; exists (S n); auto.
      * right; right; exists (S n); auto.
    + match goal with TAIL : library_steps _ _ (dead m) _ _ |- _ =>
        destruct (library_dead_steps _ _ _ _ _ TAIL) as [ES EQ] end; subst.
      right; left; exists 0%nat; auto.
    + match goal with TAIL : library_steps _ _ (dead m) _ _ |- _ =>
        destruct (library_dead_steps _ _ _ _ _ TAIL) as [ES EQ] end; subst.
      right; right; exists 0%nat; auto.
Qed.

Theorem exit_history_never_returns : forall ge cell code k m events value rest after,
  ~ library_steps ge cell (live (Callstate exit_definition [Vint code] k m)) events
    (live (Returnstate value rest after)).
Proof.
  intros ge cell code k m events value rest after RUN.
  destruct (exit_histories _ _ _ _ _ _ _ RUN) as [[n [_ EQ]]|[[n [_ EQ]]|[n [_ EQ]]]]; discriminate.
Qed.
