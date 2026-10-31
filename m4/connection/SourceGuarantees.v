(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-decoder.prefixes: Universal preservation and enabled progress for composed source paths. *)
From Coq Require Import List.
From compcert Require Import Values Memory Events Clight.
Require Import Machine Deterministic StoreSteps LibraryMachine LibraryPreservation LibraryControl CallPaths CallProgress SourcePaths.
Import ListNotations.
Definition procedure_guarantee ge cell (P : mem -> Prop) R start :=
  (forall events target, library_steps ge cell (live start) events target -> P (routine_memory target)) /\
  procedure_progress ge cell start R.
Theorem source_returns_guarantee : forall ge cell P R start,
  source_returns ge P R start -> procedure_guarantee ge cell P R start.
Proof.
  intros ge cell P R start [n [value [after [PATH POST]]]]. split.
  - intros events target RUN.
    destruct (store_path_library_projection _ _ _ _ _ _ _ PATH _ _ RUN) as [old [_ OLD]].
    exact (proj1 (store_path_prefix_invariant _ _ _ _ _ _ _ _ _ PATH OLD)).
  - intros events s RUN.
    destruct (store_path_library_projection _ _ _ _ _ _ _ PATH _ _ RUN) as [old [_ OLD]].
    destruct (store_path_defined_prefix _ _ _ _ _ _ _ _ _ PATH OLD) as [SAME|[next STEP]].
    + left;exists value,after;auto.
    + right;exists (original_event (source_step E0)),(live next);split.
      * unfold control_progress;cbn;repeat split;discriminate.
      * constructor;exact STEP.
Qed.
Theorem source_path_guarantee : forall ge cell P R start count last,
  store_path ge P start count last -> procedure_guarantee ge cell P R last ->
  procedure_guarantee ge cell P R start.
Proof.
  intros ge cell P R start count last PATH [MEMORY PROGRESS]. split.
  - intros events target RUN.
    destruct (source_path_caller_prefix _ _ _ _ _ _ PATH _ _ RUN)
      as [[n [s [remaining [_ [_ [SAME TAIL]]]]]]|[[n [m [_ [_ [SAME GOOD]]]]]|[rest [_ AFTER]]]].
    + subst target;cbn;eapply store_path_initial;eassumption.
    + subst target;exact GOOD.
    + eapply MEMORY;exact AFTER.
  - intros events current RUN.
    destruct (source_path_caller_prefix _ _ _ _ _ _ PATH _ _ RUN)
      as [[n [s [remaining [_ [_ [SAME TAIL]]]]]]|[[n [m [_ [_ [SAME GOOD]]]]]|[rest [_ AFTER]]]].
    + inversion SAME;subst s. inversion TAIL;subst.
      * apply (PROGRESS []);constructor.
      * right;exists (original_event (source_step E0)),(live next);split.
        -- unfold control_progress;cbn;repeat split;discriminate.
        -- constructor. match goal with EDGE : store_edge _ _ _ |- _ => destruct EDGE as [IN [REAL _]] end.
           apply internal;assumption.
    + discriminate.
    + exact (PROGRESS _ _ AFTER).
Qed.
Lemma source_returns_run : forall ge cell P R start,
  source_returns ge P R start -> exists events value after,
  library_steps ge cell (live start) events (live (Returnstate value Kstop after)) /\
  Forall control_progress events /\ R value after.
Proof.
  intros ge cell P R start [n [value [after [PATH POST]]]].
  exists (map original_event (repeat (source_step E0) n)),value,after.
  split; [apply original_runs_preserved;eapply store_path_actual;exact PATH|].
  split; [|exact POST]. clear PATH. induction n;cbn;constructor;auto.
  unfold control_progress;cbn;repeat split;discriminate.
Qed.
