(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-decoder.prefixes: Compose actual memcmp effects with certified source continuations. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers Values Memory Events Clight.
Require Import Machine Library LibraryMachine LibraryControl CallProgress SourcePaths
  SourceGuarantees ComparisonRuns.
Import ListNotations.
Theorem memcmp_caller_guarantee : forall ge cell m left right count k P R,
  memcmp_owned m left right count -> P m ->
  (forall value, memcmp_result m left right count value ->
    source_returns ge P R (Returnstate (Vint value) k m)) ->
  procedure_guarantee ge cell P R (Callstate memcmp_definition (comparison_args left right count) k m).
Proof.
  intros ge cell m left right count k P R OWN PM RETURN. split.
  - intros events target RUN.
    destruct (memcmp_run_cases _ _ _ _ _ _ _ _ _ OWN RUN)
      as [[n [ES TARGET]]|[[n [ES TARGET]]|[n [value [rest [RESULT [ES AFTER]]]]]]].
    + subst target;exact PM.
    + subst target;exact PM.
    + exact (proj1 (source_returns_guarantee ge cell P R _ (RETURN value RESULT)) rest _ AFTER).
  - intros events current RUN.
    destruct (memcmp_run_cases _ _ _ _ _ _ _ _ _ OWN RUN)
      as [[n [ES TARGET]]|[[n [ES TARGET]]|[n [value [rest [RESULT [ES AFTER]]]]]]].
    + inversion TARGET;subst current. destruct (memcmp_progress _ _ _ _ OWN) as [value RESULT].
      right;exists (memcmp_returned left right count value),(live (Returnstate (Vint value) k m));split.
      * unfold control_progress;cbn;repeat split;discriminate.
      * apply memcmp_step;exact RESULT.
    + discriminate.
    + exact (proj2 (source_returns_guarantee ge cell P R _ (RETURN value RESULT)) rest _ AFTER).
Qed.
Theorem memcmp_caller_run : forall ge cell m left right count k P R,
  memcmp_owned m left right count ->
  (forall value, memcmp_result m left right count value ->
    source_returns ge P R (Returnstate (Vint value) k m)) ->
  exists events value after,
    library_steps ge cell (live (Callstate memcmp_definition (comparison_args left right count) k m))
      events (live (Returnstate value Kstop after)) /\ Forall control_progress events /\ R value after.
Proof.
  intros ge cell m left right count k P R OWN RETURN.
  destruct (memcmp_progress _ _ _ _ OWN) as [comparison RESULT].
  destruct (source_returns_run ge cell P R _ (RETURN comparison RESULT)) as [events [value [after [RUN [PROGRESS POST]]]]].
  exists (memcmp_returned left right count comparison :: events),value,after.
  split; [econstructor; [apply memcmp_step;exact RESULT|exact RUN]|].
  split; [|exact POST]. constructor; [|exact PROGRESS].
  unfold control_progress;cbn;repeat split;discriminate.
Qed.
