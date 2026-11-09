(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Preserve the actual Clight caller across each admitted primitive boundary. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps AST Values Memory Events Ctypes Cop Clight.
Require Import Machine LibraryMachine CallContexts.
From EntryNative Require Import NativeHandoffMachine.
Import ListNotations.

Theorem plug_entry_handoff_step ge cell before event after suffix :
  is_call_cont suffix -> entry_handoff_step ge cell before event after ->
  entry_handoff_step ge cell (plug_machine before suffix) event (plug_machine after suffix).
Proof.
  intros CALL STEP; inversion STEP; subst; cbn.
  - apply entry_library_step; apply plug_library_step; assumption.
  - apply entry_format_step; assumption.
  - apply entry_format_loss_step; assumption.
  - apply entry_flags_step; assumption.
  - apply entry_flags_loss_step; assumption.
  - apply entry_exec_error_step; assumption.
  - apply entry_exec_loss_step; assumption.
  - apply entry_exec_image_step.
  - apply entry_format_wait; assumption.
  - apply entry_flags_wait.
  - apply entry_exec_wait.
Qed.

Theorem unplug_entry_handoff_step ge cell state event after suffix :
  is_call_cont suffix -> ~ local_return state ->
  entry_handoff_step ge cell (live (plug_state state suffix)) event after ->
  exists next, entry_handoff_step ge cell (live state) event next /\ after = plug_machine next suffix.
Proof.
  intros CALL NOTRETURN STEP; inversion STEP; subst.
  - match goal with LIBRARY : library_step _ _ _ _ _ |- _ =>
      destruct (unplug_library_step _ _ _ _ _ _ CALL NOTRETURN LIBRARY)
        as [next [REAL SAME]] end.
    exists next; split; [apply entry_library_step; exact REAL|exact SAME].
  - destruct state; cbn in *; try discriminate.
    match goal with EQ : Callstate _ _ _ _ = Callstate _ _ _ _ |- _ => inversion EQ; subst end.
    eexists; split; [apply entry_format_step; eassumption|reflexivity].
  - destruct state; cbn in *; try discriminate.
    match goal with EQ : Callstate _ _ _ _ = Callstate _ _ _ _ |- _ => inversion EQ; subst end.
    eexists; split; [apply entry_format_loss_step; eassumption|reflexivity].
  - destruct state; cbn in *; try discriminate.
    match goal with EQ : Callstate _ _ _ _ = Callstate _ _ _ _ |- _ => inversion EQ; subst end.
    eexists; split; [apply entry_flags_step; eassumption|reflexivity].
  - destruct state; cbn in *; try discriminate.
    match goal with EQ : Callstate _ _ _ _ = Callstate _ _ _ _ |- _ => inversion EQ; subst end.
    eexists; split; [apply entry_flags_loss_step; eassumption|reflexivity].
  - destruct state; cbn in *; try discriminate.
    match goal with EQ : Callstate _ _ _ _ = Callstate _ _ _ _ |- _ => inversion EQ; subst end.
    eexists; split; [apply entry_exec_error_step; eassumption|reflexivity].
  - destruct state; cbn in *; try discriminate.
    match goal with EQ : Callstate _ _ _ _ = Callstate _ _ _ _ |- _ => inversion EQ; subst end.
    eexists; split; [apply entry_exec_loss_step; eassumption|reflexivity].
  - destruct state; cbn in *; try discriminate.
    match goal with EQ : Callstate _ _ _ _ = Callstate _ _ _ _ |- _ => inversion EQ; subst end.
    eexists; split; [apply entry_exec_image_step|reflexivity].
  - destruct state; cbn in *; try discriminate.
    match goal with EQ : Callstate _ _ _ _ = Callstate _ _ _ _ |- _ => inversion EQ; subst end.
    eexists; split; [apply entry_format_wait; eassumption|reflexivity].
  - destruct state; cbn in *; try discriminate.
    match goal with EQ : Callstate _ _ _ _ = Callstate _ _ _ _ |- _ => inversion EQ; subst end.
    eexists; split; [apply entry_flags_wait|reflexivity].
  - destruct state; cbn in *; try discriminate.
    match goal with EQ : Callstate _ _ _ _ = Callstate _ _ _ _ |- _ => inversion EQ; subst end.
    eexists; split; [apply entry_exec_wait|reflexivity].
Qed.

Theorem plug_entry_handoff_steps ge cell before events after suffix :
  is_call_cont suffix -> entry_handoff_steps ge cell before events after ->
  entry_handoff_steps ge cell (plug_machine before suffix) events (plug_machine after suffix).
Proof.
  intros CALL RUN; induction RUN; [constructor|].
  econstructor; [apply plug_entry_handoff_step; eassumption|exact IHRUN].
Qed.

Theorem entry_caller_run_decomposition ge cell suffix start events target :
  is_call_cont suffix ->
  entry_handoff_steps ge cell (live (plug_state start suffix)) events target ->
  (exists local_target, entry_handoff_steps ge cell (live start) events local_target /\
    target = plug_machine local_target suffix) \/
  (exists before after value m,
    events = before ++ after /\
    entry_handoff_steps ge cell (live start) before (live (Returnstate value Kstop m)) /\
    entry_handoff_steps ge cell (live (Returnstate value suffix m)) after target).
Proof.
  revert start; induction events as [|event rest IH]; intros start CALL RUN.
  - inversion RUN; subst. left; exists (live start); split; [constructor|reflexivity].
  - destruct (local_return_dec start) as [[value [m SAME]]|NOTRETURN].
    + subst; right; exists [], (event :: rest), value, m; split; [reflexivity|].
      split; [constructor|exact RUN].
    + inversion RUN; subst.
      match goal with STEP : entry_handoff_step _ _ _ _ _ |- _ =>
        destruct (unplug_entry_handoff_step _ _ _ _ _ _ CALL NOTRETURN STEP)
          as [local_middle [REAL SAME]] end.
      subst middle; destruct local_middle as [next|m]; cbn in *.
      * match goal with TAIL : entry_handoff_steps _ _ (live (plug_state next suffix)) _ _ |- _ =>
          destruct (IH next CALL TAIL)
            as [[last [LOCAL SAME]]|
                [before [after [value [m [EVENTS [LOCAL CONTINUATION]]]]]]] end.
        -- left; exists last; split; [econstructor; eassumption|exact SAME].
        -- right; exists (event :: before), after, value, m; split; [cbn; congruence|].
           split; [econstructor; eassumption|exact CONTINUATION].
      * match goal with TAIL : entry_handoff_steps _ _ (dead m) _ _ |- _ =>
          destruct (entry_handoff_dead_steps _ _ _ _ _ TAIL) as [EVENTS SAME] end.
        subst; left; exists (dead m); split; [econstructor; [exact REAL|constructor]|reflexivity].
Qed.
