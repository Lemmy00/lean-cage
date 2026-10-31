(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-callers.continuation: Instantiate caller progress with the preserved source theorems. *)
From Coq Require Import List.
From compcert Require Import Integers Values Memory Clight.
Require Import Slice IO Machine WriteMemory WriteAll Library LibraryMachine LibraryPreservation
  LibraryControl Fault CallProgressDraft ExitControlDraft.
Import ListNotations.

Lemma write_ordinary_control : forall ev, ordinary ev -> control_progress (original_event ev).
Proof. intros ev ORD; destruct ev; unfold ordinary, control_progress in *; cbn in *; intuition discriminate. Qed.

Theorem write_procedure_progress : forall q input m,
  write_owned q input m ->
  procedure_progress (Clight.globalenv Slice.prog) (cell_of q) (WriteAll.initial_state q m)
    (fun value after => write_owned q input after /\
      (value = Vint Int.zero \/ value = Vint Int.mone)).
Proof.
  intros q input m OWN events s RUN.
  destruct (write_all_library_projection _ _ _ _ _ OWN RUN) as [old [ES ORIGINAL]].
  destruct (write_all_defined_prefix _ _ _ _ _ OWN ORIGINAL) as [[value [after EQ]]|[ev [target [ORD STEP]]]].
  - subst s; left; exists (Vint value), after; split; [reflexivity|].
    split; [exact (proj1 (write_all_prefix_safety _ _ _ _ _ OWN ORIGINAL))|].
    destruct (write_all_return_exact _ _ _ _ _ _ OWN ORIGINAL) as [[V _]|[V _]]; auto.
  - right; exists (original_event ev), target; split; [apply write_ordinary_control; exact ORD|constructor; exact STEP].
Qed.

Theorem fault_procedure_progress : forall cell m mode name xs ys,
  fault_input (Clight.globalenv Slice.prog) m mode name xs ys ->
  procedure_progress (Clight.globalenv Slice.prog) cell (fault_initial name Kstop m)
    (fun value after => value = fault_value xs ys /\ after = m).
Proof.
  intros cell m mode name xs ys OWN events s RUN.
  destruct (fault_defined_prefix _ _ _ _ _ _ _ _ OWN RUN) as [EQ|PROGRESS].
  - left; exists (fault_value xs ys), m; auto.
  - right; exact PROGRESS.
Qed.

Theorem exit_live_progress : forall ge cell code k m,
  live_progress ge cell (Callstate exit_definition [Vint code] k m).
Proof.
  intros ge cell code k m events s RUN.
  destruct (exit_histories _ _ _ _ _ _ _ RUN) as [[n [ES EQ]]|[[n [ES EQ]]|[n [ES EQ]]]];
    try discriminate. inversion EQ; subst.
  exists (exit_requested code), (dead m); split.
  - unfold control_progress; cbn; repeat split; discriminate.
  - apply exit_step.
Qed.
