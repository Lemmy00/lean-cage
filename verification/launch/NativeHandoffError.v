(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Reuse actual source errno normalization under the entry machine. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Slice IO Machine ErrorNumber Deterministic WriteAll StoreSteps LibraryMachine.
From EntryNative Require Import EntrySource NativeHandoffMachine HandoffRegion.
Import ListNotations.

Lemma entry_errno_step_exact ge cell k m event target :
  entry_handoff_step ge cell
    (live (Callstate (External errno_function [] (tptr tint) cc_default) [] k m)) event target ->
  exists original, event = entry_library (original_event original) /\
    Machine.step ge cell
      (live (Callstate (External errno_function [] (tptr tint) cc_default) [] k m)) original target.
Proof.
  intros STEP; inversion STEP; subst; try discriminate.
  match goal with BASE : library_step _ _ _ _ _ |- _ => inversion BASE; subst; try discriminate end.
  - eexists; split; [reflexivity|eassumption].
  - match goal with READY : library_ready _ _ |- _ => inversion READY end.
Qed.

Lemma entry_certain_boundary ge cell state event next actual target :
  certain_step ge cell state event next ->
  entry_handoff_step ge cell (live state) actual target ->
  (actual = entry_library (original_event event) /\ target = live next) \/
  (actual = entry_library (original_event loss_step) /\ target = dead (memory_of state)).
Proof.
  intros [ORD [REAL [MEM CASES]]] STEP.
  assert (ORIGINAL : exists old, actual = entry_library (original_event old) /\
      Machine.step ge cell (live state) old target).
  { destruct ORD as [SOURCE|ERRNO]; subst event.
    - assert (INTERNAL : internal_state state) by (inversion REAL; subst; assumption).
      exact (entry_internal_step_exact _ _ _ _ _ INTERNAL STEP).
    - inversion REAL; subst; try discriminate.
      exact (entry_errno_step_exact _ _ _ _ _ _ STEP). }
  destruct ORIGINAL as [old [ACTUAL BASE]]; subst actual.
  destruct (CASES _ _ BASE) as [[EVENT TARGET]|[EVENT TARGET]]; subst; auto.
Qed.

Lemma entry_routine_not_waiting event : routine_event event ->
  handoff_waiting (entry_library (original_event event)) = false /\
  handoff_image (entry_library (original_event event)) = false.
Proof. intros [SAME|SAME]; subst; split; reflexivity. Qed.

Theorem handoff_region_execution ge cell P R start schedule last remaining :
  execution ge cell start schedule last -> P (memory_of start) ->
  handoff_region ge cell P R remaining last ->
  handoff_region ge cell P R (length schedule + remaining) start.
Proof.
  intros SCRIPT; induction SCRIPT; intros GOOD CERT; cbn; auto.
  pose proof H as [ORD [REAL [MEM CASES]]].
  destruct (entry_routine_not_waiting _ ORD) as [WAIT IMAGE].
  eapply handoff_region_next; [exact GOOD| |].
  - exists (entry_library (original_event ev)), next; split; [exact WAIT|].
    split; [exact IMAGE|apply entry_library_step; apply original_step; exact REAL].
  - intros event target STEP.
    destruct (entry_certain_boundary _ _ _ _ _ _ _ H STEP) as [[EVENT TARGET]|[EVENT TARGET]]; subst.
    + right; right; exists next; split; [reflexivity|]; split; [exact WAIT|].
      split; [exact IMAGE|apply IHSCRIPT; [rewrite MEM; exact GOOD|exact CERT]].
    + right; left; exists (memory_of s); auto.
Qed.

Lemma current_entry_error_symbols : WriteAll.symbols (Clight.globalenv EntrySource.prog).
Proof. split; eexists; split; vm_compute; reflexivity. Qed.

Theorem current_entry_error_region cell m error suffix (P : mem -> Prop) R remaining :
  initialized_errno cell m error -> is_call_cont suffix -> P m ->
  handoff_region (Clight.globalenv EntrySource.prog) cell P R remaining
    (Returnstate (Vint (normalize error)) suffix m) ->
  handoff_region (Clight.globalenv EntrySource.prog) cell P R
    (source_length error + remaining)
    (Callstate (Internal EntrySource.f_error_number) [] suffix m).
Proof.
  intros OWN CALL GOOD NEXT.
  assert (CONT : call_cont suffix = suffix) by (destruct suffix; cbn in *; try contradiction; reflexivity).
  destruct (source_execution _ _ _ _ suffix current_entry_error_symbols OWN)
    as [schedule [SCRIPT [LENGTH QUERIES]]].
  rewrite CONT in SCRIPT.
  rewrite <- LENGTH; eapply handoff_region_execution; [exact SCRIPT|exact GOOD|exact NEXT].
Qed.

Theorem current_entry_error_range error :
  (1 <= Int.signed (normalize error) <= 4095)%Z.
Proof. apply normalize_range. Qed.

Theorem current_entry_error_region_exists cell m error suffix (P : mem -> Prop) R remaining :
  initialized_errno cell m error -> is_call_cont suffix -> P m ->
  handoff_region (Clight.globalenv EntrySource.prog) cell P R remaining
    (Returnstate (Vint (normalize error)) suffix m) ->
  exists events endpoint,
    entry_handoff_steps (Clight.globalenv EntrySource.prog) cell
      (live (Callstate (Internal EntrySource.f_error_number) [] suffix m)) events (live endpoint) /\
    handoff_no_images events /\ P (memory_of endpoint) /\ R endpoint.
Proof.
  intros OWN CALL GOOD NEXT.
  destruct (handoff_region_actual _ _ _ _ _ _
    (current_entry_error_region cell m error suffix P R remaining OWN CALL GOOD NEXT))
    as [events [endpoint [RUN [COST REST]]]].
  exists events, endpoint; auto.
Qed.
