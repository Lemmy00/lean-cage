(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-decoder.prefixes: Every actual comparison history retains waits and loss. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers Values Memory Clight.
Require Import Machine Library LibraryMachine LibraryPreservation ComparisonControl.
Import ListNotations.
Open Scope Z_scope.
Theorem memcmp_run_cases : forall ge cell m left right count k events target,
  memcmp_owned m left right count ->
  library_steps ge cell (live (Callstate memcmp_definition (comparison_args left right count) k m)) events target ->
  (exists n, events=repeat library_wait n /\
    target=live (Callstate memcmp_definition (comparison_args left right count) k m)) \/
  (exists n, events=repeat library_wait n ++ [original_event loss_step] /\ target=dead m) \/
  (exists n value rest, memcmp_result m left right count value /\
    events=repeat library_wait n ++ memcmp_returned left right count value :: rest /\
    library_steps ge cell (live (Returnstate (Vint value) k m)) rest target).
Proof.
  intros ge cell m left right count k events target OWN RUN.
  remember (live (Callstate memcmp_definition (comparison_args left right count) k m)) as initial eqn:INIT.
  induction RUN as [s|s ev mid rest last STEP RUN IH]; subst s.
  - left;exists 0%nat;auto.
  - destruct (memcmp_boundary_cases _ _ _ _ _ _ _ _ _ OWN STEP)
      as [[value [RES [EV TARGET]]]|[[EV TARGET]|[EV TARGET]]]; subst.
    + right;right;exists 0%nat,value,rest;auto.
    + destruct (IH eq_refl) as [[n [ES TARGET]]|[[n [ES TARGET]]|[n [value [tail [RES [ES AFTER]]]]]]]; subst.
      * left;exists (S n);auto.
      * right;left;exists (S n);auto.
      * right;right;exists (S n),value,tail;auto.
    + destruct (library_dead_steps _ _ _ _ _ RUN) as [ES TARGET];subst.
      right;left;exists 0%nat;auto.
Qed.
