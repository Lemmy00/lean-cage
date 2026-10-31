(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.reporting: Preserve a caller invariant through every complete write_all history. *)
From Coq Require Import List.
From compcert Require Import Integers Values Memory Clight.
Require Import Slice IO Machine Deterministic WriteMemory WriteAll LibraryMachine LibraryPreservation
  LibraryControl CallProgress SourceGuarantees WriteEffects.
Import ListNotations.
Definition write_memory_post q input before value after :=
  tls_history (cell_of q) before after /\ write_owned q input after /\
  (value=Vint Int.zero \/ value=Vint Int.mone).
Lemma write_ordinary_progress : forall ev,ordinary ev -> control_progress (original_event ev).
Proof. intros ev ORD;destruct ev;unfold ordinary,control_progress in *;cbn in *;intuition discriminate. Qed.

Theorem write_source_guarantee : forall q input m (P : mem -> Prop),
  write_owned q input m ->
  (forall after,tls_history (cell_of q) m after -> P after) ->
  procedure_guarantee (Clight.globalenv Slice.prog) (cell_of q) P (write_memory_post q input m)
    (WriteAll.initial_state q m).
Proof.
  intros q input m P OWN PRESERVE;split.
  - intros events target RUN;apply PRESERVE;eapply write_all_tls_history;[exact OWN|exact RUN].
  - intros events s RUN.
    pose proof (write_all_tls_history _ _ _ _ _ OWN RUN) as HISTORY.
    destruct (write_all_library_projection _ _ _ _ _ OWN RUN) as [old [ES ORIGINAL]].
    destruct (write_all_defined_prefix _ _ _ _ _ OWN ORIGINAL)
      as [[value [after EQ]]|[ev [target [ORD STEP]]]].
    + subst s;left;exists (Vint value),after;split;[reflexivity|].
      split;[exact HISTORY|]. split;[exact (proj1 (write_all_prefix_safety _ _ _ _ _ OWN ORIGINAL))|].
      destruct (write_all_return_exact _ _ _ _ _ _ OWN ORIGINAL) as [[VALUE _]|[VALUE _]];auto.
    + right;exists (original_event ev),target;split;[apply write_ordinary_progress;exact ORD|constructor;exact STEP].
Qed.

Require Import WriteCallers.
Definition detailed_write_post q input m value after :=
  tls_history (cell_of q) m after /\ exists events,
    Machine.steps (Clight.globalenv Slice.prog) (cell_of q) (live (WriteAll.initial_state q m)) events
      (live (Returnstate value Kstop after)) /\ write_return_post q input events value after.
Theorem write_detailed_guarantee : forall q input m (P : mem -> Prop),
  write_owned q input m ->
  (forall after,tls_history (cell_of q) m after -> P after) ->
  procedure_guarantee (Clight.globalenv Slice.prog) (cell_of q) P (detailed_write_post q input m)
    (WriteAll.initial_state q m).
Proof.
  intros q input m P OWN PRESERVE;split.
  - intros events target RUN;apply PRESERVE;eapply write_all_tls_history;[exact OWN|exact RUN].
  - intros events s RUN.
    pose proof (write_all_tls_history _ _ _ _ _ OWN RUN) as HISTORY.
    destruct (write_all_library_projection _ _ _ _ _ OWN RUN) as [old [ES ORIGINAL]].
    destruct (write_all_defined_prefix _ _ _ _ _ OWN ORIGINAL)
      as [[value [after EQ]]|[ev [target [ORD STEP]]]].
    + subst s;left;exists (Vint value),after;split;[reflexivity|].
      split;[exact HISTORY|]. exists old;split;[exact ORIGINAL|].
      split;[exact (proj1 (write_all_prefix_safety _ _ _ _ _ OWN ORIGINAL))|].
      exact (write_all_return_exact _ _ _ _ _ _ OWN ORIGINAL).
    + right;exists (original_event ev),target;split;[apply write_ordinary_progress;exact ORD|constructor;exact STEP].
Qed.
