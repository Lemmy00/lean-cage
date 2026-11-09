(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.effects: Classify every return, wait and loss at the fixed handoff primitives. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import IO Machine LibraryMachine LibraryPreservation ErrorNumber ProcessEffects.
From EntryNative Require Import NativeHandoffMachine.
Import ListNotations.
Open Scope Z_scope.

Lemma handoff_format_library_only_loss ge cell output offset value k before event target :
  library_step ge cell
    (live (Callstate entry_decimal_definition [Vptr output offset; Vlong value] k before)) event target ->
  event = original_event loss_step /\ target = dead before.
Proof.
  intros STEP; inversion STEP; subst; try discriminate.
  - inversion H; subst; cbn in *; try contradiction; auto;
      match goal with BOUNDARY : boundary _ _ _ |- _ =>
        inversion BOUNDARY; subst; destruct (operation q); discriminate end.
  - match goal with READY : library_ready _ _ |- _ => inversion READY end.
Qed.

Theorem handoff_format_cases ge cell output offset value k before event target :
  entry_handoff_step ge cell
    (live (Callstate entry_decimal_definition [Vptr output offset; Vlong value] k before)) event target ->
  (exists returned after,
    entry_format_owned before output offset /\
    entry_format_result cell before output offset returned after /\
    event = entry_formatted output offset value returned /\
    target = live (Returnstate (Vint returned) k after)) \/
  (event = entry_primitive_wait /\ target = live
    (Callstate entry_decimal_definition [Vptr output offset; Vlong value] k before)) \/
  (exists after, entry_format_partial cell before output offset after /\
    event = entry_format_lost output offset value /\ target = dead after) \/
  (event = entry_library (original_event loss_step) /\ target = dead before).
Proof.
  intros STEP; inversion STEP; subst; try discriminate.
  - destruct (handoff_format_library_only_loss _ _ _ _ _ _ _ _ _ H) as [EVENT TARGET]; subst.
    right; right; right; split; reflexivity.
  - left; exists returned,after; split; [assumption|]. split; [assumption|]. split; reflexivity.
  - right; right; left; exists after; split; [assumption|]. split; reflexivity.
  - right; left; split; reflexivity.
Qed.

Lemma handoff_flags_library_only_loss ge cell descriptor flags k before event target :
  library_step ge cell
    (live (Callstate entry_flags_definition [Vint descriptor; Vint flags] k before)) event target ->
  event = original_event loss_step /\ target = dead before.
Proof.
  intros STEP; inversion STEP; subst; try discriminate.
  - inversion H; subst; cbn in *; try contradiction; auto;
      match goal with BOUNDARY : boundary _ _ _ |- _ =>
        inversion BOUNDARY; subst; destruct (operation q); discriminate end.
  - match goal with READY : library_ready _ _ |- _ => inversion READY end.
Qed.

Theorem handoff_flags_cases ge cell descriptor flags k before event target :
  entry_handoff_step ge cell
    (live (Callstate entry_flags_definition [Vint descriptor; Vint flags] k before)) event target ->
  (exists returned after,
    entry_errno_frame cell before after /\ entry_errno_ready cell after /\
    event = entry_flags_returned descriptor flags returned /\
    target = live (Returnstate (Vint returned) k after)) \/
  (event = entry_primitive_wait /\ target = live
    (Callstate entry_flags_definition [Vint descriptor; Vint flags] k before)) \/
  (exists after, entry_errno_partial cell before after /\
    event = entry_flags_lost descriptor flags /\ target = dead after) \/
  (event = entry_library (original_event loss_step) /\ target = dead before).
Proof.
  intros STEP; inversion STEP; subst; try discriminate.
  - destruct (handoff_flags_library_only_loss _ _ _ _ _ _ _ _ H) as [EVENT TARGET]; subst.
    right; right; right; split; reflexivity.
  - left; exists returned,after; split; [assumption|]. split; [assumption|]. split; reflexivity.
  - right; right; left; exists after; split; [assumption|]. split; reflexivity.
  - right; left; split; reflexivity.
Qed.

Theorem handoff_format_failure_result cell before output offset :
  entry_errno_ready cell before -> entry_format_result cell before output offset Int.mone before.
Proof.
  intros ERRNO; constructor.
  - apply Mem.unchanged_on_refl.
  - intros; reflexivity.
  - exact ERRNO.
  - intros IMPOSSIBLE; change (0 < -1 < 32) in IMPOSSIBLE; lia.
Qed.

From EntryNative Require Import HandoffRegion.

Theorem handoff_format_region ge cell P R remaining output offset value k before :
  P before -> entry_format_owned before output offset -> entry_errno_ready cell before ->
  (forall after, entry_format_partial cell before output offset after -> P after) ->
  (forall returned after, entry_format_result cell before output offset returned after ->
    handoff_region ge cell P R remaining (Returnstate (Vint returned) k after)) ->
  handoff_region ge cell P R (S remaining)
    (Callstate entry_decimal_definition [Vptr output offset; Vlong value] k before).
Proof.
  intros GOOD OWN ERRNO PARTIAL RETURN; eapply handoff_region_next; [exact GOOD| |].
  - exists (entry_formatted output offset value Int.mone), (Returnstate (Vint Int.mone) k before).
    split; [reflexivity|]. split; [reflexivity|].
    apply entry_format_step; [exact OWN|apply handoff_format_failure_result; exact ERRNO].
  - intros event target STEP; destruct (handoff_format_cases _ _ _ _ _ _ _ _ _ STEP)
      as [[returned [after [OWN' [RESULT [EVENT TARGET]]]]]|
          [[EVENT TARGET]|[[after [RESULT [EVENT TARGET]]]|[EVENT TARGET]]]]; subst.
    + right; right; exists (Returnstate (Vint returned) k after).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|apply RETURN; exact RESULT].
    + left; split; reflexivity.
    + right; left; exists after; split; [reflexivity|]. split; [apply PARTIAL; exact RESULT|reflexivity].
    + right; left; exists before; split; [reflexivity|]. split; [exact GOOD|reflexivity].
Qed.

Theorem handoff_flags_region ge cell P R remaining descriptor flags k before :
  P before -> entry_errno_ready cell before ->
  (forall after, entry_errno_partial cell before after -> P after) ->
  (forall returned after, entry_errno_frame cell before after -> entry_errno_ready cell after ->
    handoff_region ge cell P R remaining (Returnstate (Vint returned) k after)) ->
  handoff_region ge cell P R (S remaining)
    (Callstate entry_flags_definition [Vint descriptor; Vint flags] k before).
Proof.
  intros GOOD ERRNO PARTIAL RETURN; eapply handoff_region_next; [exact GOOD| |].
  - exists (entry_flags_returned descriptor flags Int.zero), (Returnstate (Vint Int.zero) k before).
    split; [reflexivity|]. split; [reflexivity|].
    apply entry_flags_step; [apply Mem.unchanged_on_refl|exact ERRNO].
  - intros event target STEP; destruct (handoff_flags_cases _ _ _ _ _ _ _ _ STEP)
      as [[returned [after [FRAME [READY [EVENT TARGET]]]]]|
          [[EVENT TARGET]|[[after [RESULT [EVENT TARGET]]]|[EVENT TARGET]]]]; subst.
    + right; right; exists (Returnstate (Vint returned) k after).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|apply RETURN; assumption].
    + left; split; reflexivity.
    + right; left; exists after; split; [reflexivity|]. split; [apply PARTIAL; exact RESULT|reflexivity].
    + right; left; exists before; split; [reflexivity|]. split; [exact GOOD|reflexivity].
Qed.
