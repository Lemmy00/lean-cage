(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.effects: Cover actual parent kill/sleep calls without a compound supervision axiom. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import IO Machine LibraryMachine.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessGlobalCalls.
Import ListNotations.

Theorem actual_parent_auxiliary_bindings :
  (exists pointer,Genv.find_symbol caller_ge _kill=Some pointer /\
    Genv.find_funct caller_ge(Vptr pointer Ptrofs.zero)=Some process_kill_definition) /\
  (exists pointer,Genv.find_symbol caller_ge _usleep=Some pointer /\
    Genv.find_funct caller_ge(Vptr pointer Ptrofs.zero)=Some process_sleep_definition).
Proof. split;eexists;split;vm_compute;reflexivity. Qed.

Lemma auxiliary_entry_only_loss ge cell before definition arguments continuation event target :
  (definition=process_kill_definition \/definition=process_sleep_definition) ->
  entry_handoff_step ge cell(live(Callstate definition arguments continuation before))event target ->
  event=entry_library(original_event loss_step) /\target=dead before.
Proof.
  intros DEFINITION STEP;destruct DEFINITION;subst definition;
    inversion STEP;subst;try discriminate.
  all:match goal with LIB:library_step _ _ _ _ _|-_=>inversion LIB;subst;try discriminate end.
  all:try match goal with ORIGINAL:Machine.step _ _ _ _ _|-_=>
    inversion ORIGINAL;subst;cbn in *;try contradiction;
    try match goal with BOUND:boundary _ _ _|-_=>inversion BOUND;subst;destruct(operation q);discriminate end
    end;auto.
  all:match goal with READY:library_ready _ _|-_=>inversion READY end.
Qed.

Theorem process_kill_cases ge cell before pid signal continuation event target :
  process_step ge cell(live(Callstate process_kill_definition[Vint pid;Vint signal]continuation before))
    event target ->
  (exists returned after,entry_errno_frame cell before after /\entry_errno_ready cell after /\
    event=process_auxiliary(auxiliary_returned auxiliary_kill pid signal returned) /\
    target=live(Returnstate(Vint returned)continuation after)) \/
  (event=process_waiting /\target=live(Callstate process_kill_definition[Vint pid;Vint signal]continuation before)) \/
  (exists after,entry_errno_partial cell before after /\
    event=process_auxiliary(auxiliary_lost auxiliary_kill pid signal) /\target=dead after) \/
  (event=process_entry(entry_library(original_event loss_step)) /\target=dead before).
Proof.
  intro STEP;inversion STEP;subst;try discriminate;eauto 12.
  destruct(auxiliary_entry_only_loss _ _ _ _ _ _ _ _ (or_introl eq_refl) H)as[EVENT TARGET];subst;auto.
Qed.

Theorem process_sleep_cases ge cell before micros continuation event target :
  process_step ge cell(live(Callstate process_sleep_definition[Vint micros]continuation before))event target ->
  (exists returned after,entry_errno_frame cell before after /\entry_errno_ready cell after /\
    event=process_auxiliary(auxiliary_returned auxiliary_sleep micros Int.zero returned) /\
    target=live(Returnstate(Vint returned)continuation after)) \/
  (event=process_waiting /\target=live(Callstate process_sleep_definition[Vint micros]continuation before)) \/
  (exists after,entry_errno_partial cell before after /\
    event=process_auxiliary(auxiliary_lost auxiliary_sleep micros Int.zero) /\target=dead after) \/
  (event=process_entry(entry_library(original_event loss_step)) /\target=dead before).
Proof.
  intro STEP;inversion STEP;subst;try discriminate;eauto 12.
  destruct(auxiliary_entry_only_loss _ _ _ _ _ _ _ _ (or_intror eq_refl) H)as[EVENT TARGET];subst;auto.
Qed.

Theorem kill_return_wait_loss_paths ge cell before pid signal continuation returned count :
  entry_errno_ready cell before ->
  process_steps ge cell(live(Callstate process_kill_definition[Vint pid;Vint signal]continuation before))
    (repeat process_waiting count++
      [process_auxiliary(auxiliary_returned auxiliary_kill pid signal returned)])
    (live(Returnstate(Vint returned)continuation before)) /\
  process_steps ge cell(live(Callstate process_kill_definition[Vint pid;Vint signal]continuation before))
    (repeat process_waiting count++[process_auxiliary(auxiliary_lost auxiliary_kill pid signal)])(dead before).
Proof.
  intro READY;induction count;cbn.
  - split;econstructor;[apply process_kill_step;[apply Mem.unchanged_on_refl|exact READY]|constructor|
      apply process_kill_loss;constructor;[apply Mem.unchanged_on_refl|intros;tauto]|constructor].
  - destruct IHcount as[RETURN LOSS];split;econstructor;[apply process_kill_waiting|exact RETURN|
      apply process_kill_waiting|exact LOSS].
Qed.

Theorem sleep_return_wait_loss_paths ge cell before micros continuation returned count :
  entry_errno_ready cell before ->
  process_steps ge cell(live(Callstate process_sleep_definition[Vint micros]continuation before))
    (repeat process_waiting count++
      [process_auxiliary(auxiliary_returned auxiliary_sleep micros Int.zero returned)])
    (live(Returnstate(Vint returned)continuation before)) /\
  process_steps ge cell(live(Callstate process_sleep_definition[Vint micros]continuation before))
    (repeat process_waiting count++[process_auxiliary(auxiliary_lost auxiliary_sleep micros Int.zero)])(dead before).
Proof.
  intro READY;induction count;cbn.
  - split;econstructor;[apply process_sleep_step;[apply Mem.unchanged_on_refl|exact READY]|constructor|
      apply process_sleep_loss;constructor;[apply Mem.unchanged_on_refl|intros;tauto]|constructor].
  - destruct IHcount as[RETURN LOSS];split;econstructor;[apply process_sleep_waiting|exact RETURN|
      apply process_sleep_waiting|exact LOSS].
Qed.
