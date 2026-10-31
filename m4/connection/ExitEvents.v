(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-callers.failure: Local report helpers cannot manufacture a different exit. *)
From Coq Require Import List.
From compcert Require Import Integers Values Memory Clight.
Require Import Slice Machine WriteMemory WriteAll LibraryMachine LibraryPreservation Fault
  CallEventsDraft ExitControlDraft.
Import ListNotations.
Definition exit_code_event code ev := match ev with exit_requested actual => actual=code | _ => True end.

Theorem exit_event_contract : forall ge cell code k m,
  event_contract ge cell (Callstate exit_definition [Vint code] k m) (exit_code_event code).
Proof.
  intros ge cell code k m events target RUN.
  destruct (exit_histories _ _ _ _ _ _ _ RUN) as [[n [ES EQ]]|[[n [ES EQ]]|[n [ES EQ]]]]; subst events.
  - apply Forall_forall; intros ev IN; apply repeat_spec in IN; subst; exact I.
  - apply Forall_app; split.
    + apply Forall_forall; intros ev IN; apply repeat_spec in IN; subst; exact I.
    + repeat constructor.
  - apply Forall_app; split.
    + apply Forall_forall; intros ev IN; apply repeat_spec in IN; subst; exact I.
    + repeat constructor.
Qed.

Theorem write_event_contract : forall q input m code,
  write_owned q input m ->
  event_contract (Clight.globalenv Slice.prog) (cell_of q) (WriteAll.initial_state q m) (exit_code_event code).
Proof.
  intros q input m code OWN events target RUN.
  destruct (write_all_library_projection _ _ _ _ _ OWN RUN) as [original [ES OLD]]; subst events.
  apply Forall_forall; intros ev IN; apply in_map_iff in IN; destruct IN as [old [EV _]]; subst; exact I.
Qed.

Theorem fault_event_contract : forall cell m mode name xs ys code,
  fault_input (Clight.globalenv Slice.prog) m mode name xs ys ->
  event_contract (Clight.globalenv Slice.prog) cell (fault_initial name Kstop m) (exit_code_event code).
Proof.
  intros cell m mode name xs ys code INPUT events target RUN.
  pose proof (fault_events_are_selectors _ _ _ _ _ _ _ actual_fault_symbols INPUT _ _ RUN) as EVENTS.
  eapply Forall_impl; [|exact EVENTS]. intros ev GOOD; destruct ev; cbn in *; tauto.
Qed.
