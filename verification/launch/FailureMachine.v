(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Additional handoff primitives cannot reopen the actual failure routine. *)
From Stdlib Require Import ZArith List String Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import IO Machine ProcessEffects LibraryMachine LibraryControl CallContexts CallProgressDraft.
From EntryNative Require Import NativeHandoffMachine NativeHandoffContexts.
From EntryFailure Require Import FailureSource FailureProgress.
Import ListNotations.

Ltac reject_new_external :=
  intros STEP ADV; inversion STEP; subst; try discriminate;
  try match goal with H : Machine.step _ _ _ _ _ |- _ =>
    inversion H; subst; cbn in * end;
  try contradiction;
  try match goal with H : boundary _ _ _ |- _ =>
    inversion H; subst;
    match goal with query : request |- _ => destruct (operation query); discriminate end end;
  try match goal with H : library_ready _ _ |- _ => inversion H end;
  unfold control_progress, control_wait in ADV; cbn in ADV; intuition discriminate.

Lemma format_has_no_library_progress ge cell m output offset value k event target :
  library_step ge cell
    (live (Callstate entry_decimal_definition [Vptr output offset; Vlong value] k m)) event target ->
  ~control_progress event.
Proof. reject_new_external. Qed.

Lemma flags_have_no_library_progress ge cell m descriptor flags k event target :
  library_step ge cell
    (live (Callstate entry_flags_definition [Vint descriptor; Vint flags] k m)) event target ->
  ~control_progress event.
Proof. reject_new_external. Qed.

Lemma exec_has_no_library_progress ge cell m path arguments environment k event target :
  library_step ge cell
    (live (Callstate entry_exec_definition [path; arguments; environment] k m)) event target ->
  ~control_progress event.
Proof. reject_new_external. Qed.

Theorem progressing_entry_step_is_library ge cell start event target :
  live_progress ge cell start ->
  entry_handoff_step ge cell (live start) event target ->
  exists original, event = entry_library original /\ library_step ge cell (live start) original target.
Proof.
  intros PROGRESS STEP.
  destruct (PROGRESS [] start (library_steps_nil _ _ _)) as [enabled [next [ADV BASE]]].
  inversion STEP; subst; try (eexists; split; [reflexivity|eassumption]).
  all: exfalso; first
    [eapply format_has_no_library_progress; eassumption
    |eapply flags_have_no_library_progress; eassumption
    |eapply exec_has_no_library_progress; eassumption].
Qed.

Theorem progressing_entry_run_is_library ge cell start events target :
  live_progress ge cell start ->
  entry_handoff_steps ge cell (live start) events target ->
  exists original, events = map entry_library original /\
    library_steps ge cell (live start) original target.
Proof.
  intros PROGRESS RUN; remember (live start) as initial eqn:INITIAL.
  revert start INITIAL PROGRESS.
  induction RUN as [state|state event middle rest target STEP RUN IH]; intros start INITIAL PROGRESS; subst state.
  - exists []; split; [reflexivity|constructor].
  - destruct (progressing_entry_step_is_library _ _ _ _ _ PROGRESS STEP)
      as [original [EVENT BASE]]; subst event.
    destruct middle as [next|after].
    + assert (TAIL : live_progress ge cell next).
      { intros more last REMAIN; apply (PROGRESS (original::more) last).
        econstructor; eassumption. }
      destruct (IH next eq_refl TAIL) as [suffix [EVENTS LIBRARY]]; subst rest.
      exists (original::suffix); split; [reflexivity|econstructor; eassumption].
    + destruct (entry_handoff_dead_steps _ _ _ _ _ RUN) as [EVENTS TARGET]; subst.
      exists [original]; split; [reflexivity|econstructor; [exact BASE|constructor]].
Qed.

Theorem current_entry_failure_never_returns cell base fd stage error events value after :
  tls_ready cell base ->
  ~entry_handoff_steps failure_ge cell (live (failure_initial fd stage error Kstop base)) events
    (live (Returnstate value Kstop after)).
Proof.
  intros TLS RUN.
  destruct (progressing_entry_run_is_library _ _ _ _ _
    (current_failure_all_prefixes cell base fd stage error Kstop TLS I) RUN)
    as [original [EVENTS LIBRARY]].
  exact (current_failure_never_returns cell base fd stage error original value after TLS LIBRARY).
Qed.

Theorem current_entry_failure_has_no_image cell base fd stage error events target :
  tls_ready cell base ->
  entry_handoff_steps failure_ge cell (live (failure_initial fd stage error Kstop base)) events target ->
  forall path arguments environment, ~In (entry_image path arguments environment) events.
Proof.
  intros TLS RUN path arguments environment IMAGE.
  destruct (progressing_entry_run_is_library _ _ _ _ _
    (current_failure_all_prefixes cell base fd stage error Kstop TLS I) RUN)
    as [original [EVENTS LIBRARY]].
  subst events; apply in_map_iff in IMAGE; destruct IMAGE as [event [SAME IN]]; discriminate.
Qed.

(* The arbitrary continuation is the real caller's; no return endpoint is assumed. *)
Theorem current_entry_failure_caller_prefix cell base fd stage error suffix events target :
  tls_ready cell base -> is_call_cont suffix ->
  entry_handoff_steps failure_ge cell (live (failure_initial fd stage error suffix base)) events target ->
  (exists local_target,
    entry_handoff_steps failure_ge cell (live (failure_initial fd stage error Kstop base)) events local_target /\
    target = plug_machine local_target suffix) /\
  (forall path arguments environment, ~In (entry_image path arguments environment) events).
Proof.
  intros TLS CALL RUN.
  change (entry_handoff_steps failure_ge cell
    (live (plug_state (failure_initial fd stage error Kstop base) suffix)) events target) in RUN.
  destruct (entry_caller_run_decomposition _ _ _ _ _ _ CALL RUN)
    as [[local_target [LOCAL SAME]]|[before [after [value [m [EVENTS [LOCAL REST]]]]]]].
  - split; [exists local_target; auto|].
    exact (current_entry_failure_has_no_image cell base fd stage error events local_target TLS LOCAL).
  - exfalso; exact (current_entry_failure_never_returns cell base fd stage error before value m TLS LOCAL).
Qed.
