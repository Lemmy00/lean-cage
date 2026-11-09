(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Preserve actual caller continuations through wait and tracing operations. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps AST Values Memory Events Ctypes Cop Clight.
Require Import Machine LibraryMachine CallContexts.
From EntryNative Require Import NativeHandoffMachine NativeHandoffContexts.
From EntryProcess Require Import ProcessMachine.
Import ListNotations.

Theorem plug_process_step ge cell before event after suffix :
  is_call_cont suffix -> process_step ge cell before event after ->
  process_step ge cell (plug_machine before suffix) event (plug_machine after suffix).
Proof.
  intros CALL STEP; inversion STEP; subst; cbn.
  - apply process_entry_step,plug_entry_handoff_step; assumption.
  - apply process_wait_step; assumption.
  - apply process_ptrace_step; assumption.
  - apply process_wait_loss; assumption.
  - apply process_ptrace_loss; assumption.
  - apply process_wait_waiting.
  - apply process_ptrace_waiting.
  - apply process_clock_step;assumption.
  - apply process_clock_loss;assumption.
  - apply process_clock_waiting;assumption.
  - apply process_kill_step;assumption.
  - apply process_sleep_step;assumption.
  - apply process_kill_loss;assumption.
  - apply process_sleep_loss;assumption.
  - apply process_kill_waiting.
  - apply process_sleep_waiting.
Qed.

Theorem unplug_process_step ge cell state event after suffix :
  is_call_cont suffix -> ~ local_return state ->
  process_step ge cell (live (plug_state state suffix)) event after ->
  exists next, process_step ge cell (live state) event next /\ after = plug_machine next suffix.
Proof.
  intros CALL NOTRETURN STEP; inversion STEP; subst.
  - match goal with ORIGINAL : entry_handoff_step _ _ _ _ _ |- _ =>
      destruct (unplug_entry_handoff_step _ _ _ _ _ _ CALL NOTRETURN ORIGINAL)
        as [next [REAL SAME]] end.
    exists next; split; [apply process_entry_step; exact REAL|exact SAME].
  - destruct state; cbn in *; try discriminate.
    match goal with EQ : Callstate _ _ _ _ = Callstate _ _ _ _ |- _ => inversion EQ; subst end.
    eexists; split; [apply process_wait_step; eassumption|reflexivity].
  - destruct state; cbn in *; try discriminate.
    match goal with EQ : Callstate _ _ _ _ = Callstate _ _ _ _ |- _ => inversion EQ; subst end.
    eexists; split; [apply process_ptrace_step; eassumption|reflexivity].
  - destruct state; cbn in *; try discriminate.
    match goal with EQ : Callstate _ _ _ _ = Callstate _ _ _ _ |- _ => inversion EQ; subst end.
    eexists; split; [apply process_wait_loss; eassumption|reflexivity].
  - destruct state; cbn in *; try discriminate.
    match goal with EQ : Callstate _ _ _ _ = Callstate _ _ _ _ |- _ => inversion EQ; subst end.
    eexists; split; [apply process_ptrace_loss; eassumption|reflexivity].
  - destruct state; cbn in *; try discriminate.
    match goal with EQ : Callstate _ _ _ _ = Callstate _ _ _ _ |- _ => inversion EQ; subst end.
    eexists; split; [apply process_wait_waiting|reflexivity].
  - destruct state; cbn in *; try discriminate.
    match goal with EQ : Callstate _ _ _ _ = Callstate _ _ _ _ |- _ => inversion EQ; subst end.
    eexists; split; [apply process_ptrace_waiting|reflexivity].
  - destruct state;cbn in *;try discriminate.
    match goal with EQ:Callstate _ _ _ _=Callstate _ _ _ _|-_=>inversion EQ;subst end.
    eexists;split;[apply process_clock_step;eassumption|reflexivity].
  - destruct state;cbn in *;try discriminate.
    match goal with EQ:Callstate _ _ _ _=Callstate _ _ _ _|-_=>inversion EQ;subst end.
    eexists;split;[apply process_clock_loss;eassumption|reflexivity].
  - destruct state;cbn in *;try discriminate.
    match goal with EQ:Callstate _ _ _ _=Callstate _ _ _ _|-_=>inversion EQ;subst end.
    eexists;split;[apply process_clock_waiting;eassumption|reflexivity].
  - destruct state;cbn in *;try discriminate.
    match goal with EQ:Callstate _ _ _ _=Callstate _ _ _ _|-_=>inversion EQ;subst end.
    eexists;split;[apply process_kill_step;eassumption|reflexivity].
  - destruct state;cbn in *;try discriminate.
    match goal with EQ:Callstate _ _ _ _=Callstate _ _ _ _|-_=>inversion EQ;subst end.
    eexists;split;[apply process_sleep_step;eassumption|reflexivity].
  - destruct state;cbn in *;try discriminate.
    match goal with EQ:Callstate _ _ _ _=Callstate _ _ _ _|-_=>inversion EQ;subst end.
    eexists;split;[apply process_kill_loss;eassumption|reflexivity].
  - destruct state;cbn in *;try discriminate.
    match goal with EQ:Callstate _ _ _ _=Callstate _ _ _ _|-_=>inversion EQ;subst end.
    eexists;split;[apply process_sleep_loss;eassumption|reflexivity].
  - destruct state;cbn in *;try discriminate.
    match goal with EQ:Callstate _ _ _ _=Callstate _ _ _ _|-_=>inversion EQ;subst end.
    eexists;split;[apply process_kill_waiting|reflexivity].
  - destruct state;cbn in *;try discriminate.
    match goal with EQ:Callstate _ _ _ _=Callstate _ _ _ _|-_=>inversion EQ;subst end.
    eexists;split;[apply process_sleep_waiting|reflexivity].
Qed.

Theorem plug_process_steps ge cell before events after suffix :
  is_call_cont suffix -> process_steps ge cell before events after ->
  process_steps ge cell (plug_machine before suffix) events (plug_machine after suffix).
Proof.
  intros CALL RUN; induction RUN; [constructor|].
  econstructor; [apply plug_process_step; eassumption|exact IHRUN].
Qed.

Theorem process_caller_run_decomposition ge cell suffix start events target :
  is_call_cont suffix ->
  process_steps ge cell (live (plug_state start suffix)) events target ->
  (exists local_target, process_steps ge cell (live start) events local_target /\
    target = plug_machine local_target suffix) \/
  (exists before after value m,
    events = before ++ after /\
    process_steps ge cell (live start) before (live (Returnstate value Kstop m)) /\
    process_steps ge cell (live (Returnstate value suffix m)) after target).
Proof.
  revert start; induction events as [|event rest IH]; intros start CALL RUN.
  - inversion RUN; subst. left; exists (live start); split; [constructor|reflexivity].
  - destruct (local_return_dec start) as [[value [m SAME]]|NOTRETURN].
    + subst; right; exists [], (event :: rest), value, m; split; [reflexivity|].
      split; [constructor|exact RUN].
    + inversion RUN; subst.
      match goal with STEP : process_step _ _ _ _ _ |- _ =>
        destruct (unplug_process_step _ _ _ _ _ _ CALL NOTRETURN STEP)
          as [local_middle [REAL SAME]] end.
      subst middle; destruct local_middle as [next|m]; cbn in *.
      * match goal with TAIL : process_steps _ _ (live (plug_state next suffix)) _ _ |- _ =>
          destruct (IH next CALL TAIL)
            as [[last [LOCAL SAME]]|
                [before [after [value [m [EVENTS [LOCAL CONTINUATION]]]]]]] end.
        -- left; exists last; split; [econstructor; eassumption|exact SAME].
        -- right; exists (event :: before), after, value, m; split; [cbn; congruence|].
           split; [econstructor; eassumption|exact CONTINUATION].
      * match goal with TAIL : process_steps _ _ (dead m) _ _ |- _ =>
          destruct (process_dead_steps _ _ _ _ _ TAIL) as [EVENTS SAME] end.
        subst; left; exists (dead m); split; [econstructor; [exact REAL|constructor]|reflexivity].
Qed.
