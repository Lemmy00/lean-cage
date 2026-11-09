(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Extra namespace primitives cannot occur in an entry-defined source run. *)
From Stdlib Require Import List String Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import IO Machine LibraryMachine LibraryControl CallProgressDraft.
From EntryNative Require Import NativeHandoffMachine HandoffRegion.
From EntryProcess Require Import ProcessMachine.
From EntryNamespace Require Import NamespaceMachine.
Import ListNotations.

Definition namespace_entry_progress event := match event with
  |entry_library library=>control_progress library
  |entry_formatted _ _ _ _|entry_flags_returned _ _ _|entry_exec_returned _ _ _ _|entry_image _ _ _=>True
  |_=>False end.
Definition namespace_entry_enabled ge cell state :=exists event target,
  namespace_entry_progress event /\entry_handoff_step ge cell(live state)event target.
Definition namespace_entry_defined ge cell state :=forall events current,
  entry_handoff_steps ge cell(live state)events(live current) ->namespace_entry_enabled ge cell current.

Lemma namespace_entry_live_is_progress ge cell state event next :
  entry_handoff_step ge cell(live state)event(live next) ->
  handoff_waiting event=false ->namespace_entry_progress event.
Proof.
  intros STEP WAIT;inversion STEP;subst;cbn[namespace_entry_progress]in *;try exact I;try discriminate.
  unfold control_progress;split;[exact WAIT|].
  split.
  - intro SAME;subst;inversion H;subst;match goal with ORIGINAL:Machine.step _ _ _ _ _|-_=>inversion ORIGINAL end.
  - split.
    + intros q bytes error SAME;subst;inversion H;subst;
        match goal with ORIGINAL:Machine.step _ _ _ _ _|-_=>inversion ORIGINAL end.
    + intros source destination bytes schedule SAME;subst;inversion H.
Qed.

Ltac reject_nonentry_call :=
  intros STEP PROGRESS;inversion STEP;subst;try discriminate;
  match goal with LIB:library_step _ _ _ _ _|-_=>inversion LIB;subst;try discriminate end;
  try match goal with ORIGINAL:Machine.step _ _ _ _ _|-_=>
    inversion ORIGINAL;subst;cbn in *;try contradiction end;
  try match goal with BOUNDARY:boundary _ _ _|-_=>
    inversion BOUNDARY;subst;match goal with q:request|-_=>destruct(operation q);discriminate end end;
  try match goal with READY:library_ready _ _|-_=>inversion READY end;
  unfold namespace_entry_progress,control_progress,control_wait in PROGRESS;cbn in PROGRESS;intuition discriminate.

Lemma namespace_ready_has_no_entry_progress ge cell state event target :
  namespace_ready state ->entry_handoff_step ge cell(live state)event target ->
  ~namespace_entry_progress event.
Proof. intro READY;inversion READY;subst;reject_nonentry_call. Qed.

Lemma namespace_waitpid_has_no_entry_progress ge cell before requested output offset options k event target :
  entry_handoff_step ge cell(live(Callstate process_wait_definition
    [Vint requested;Vptr output offset;Vint options]k before))event target ->
  ~namespace_entry_progress event.
Proof. reject_nonentry_call. Qed.
Lemma namespace_ptrace_has_no_entry_progress ge cell before request child address data k event target :
  entry_handoff_step ge cell(live(Callstate process_ptrace_definition
    [Vint request;Vint child;address;data]k before))event target ->
  ~namespace_entry_progress event.
Proof. reject_nonentry_call. Qed.
Lemma namespace_clock_has_no_entry_progress ge cell before clock output offset k event target :
  entry_handoff_step ge cell(live(Callstate process_clock_definition
    [Vint clock;Vptr output offset]k before))event target ->
  ~namespace_entry_progress event.
Proof. reject_nonentry_call. Qed.
Lemma namespace_kill_has_no_entry_progress ge cell before pid signal k event target :
  entry_handoff_step ge cell(live(Callstate process_kill_definition
    [Vint pid;Vint signal]k before))event target ->
  ~namespace_entry_progress event.
Proof. reject_nonentry_call. Qed.
Lemma namespace_sleep_has_no_entry_progress ge cell before micros k event target :
  entry_handoff_step ge cell(live(Callstate process_sleep_definition[Vint micros]k before))event target ->
  ~namespace_entry_progress event.
Proof. reject_nonentry_call. Qed.

Theorem namespace_enabled_step_projects ge cell state event target :
  namespace_entry_enabled ge cell state ->namespace_step ge cell(live state)event target ->
  exists actual,event=namespace_process(process_entry actual) /\entry_handoff_step ge cell(live state)actual target.
Proof.
  intros[enabled[next[ADVANCE ENABLED]]]STEP.
  assert(OUTSIDE:~namespace_ready state).
  { intro READY;eapply namespace_ready_has_no_entry_progress;eassumption. }
  destruct(namespace_process_projection _ _ _ _ _ OUTSIDE STEP)as[original[EVENT PROCESS]];subst event.
  inversion PROCESS;subst;try(eexists;split;[reflexivity|eassumption]).
  all:exfalso;first[eapply namespace_waitpid_has_no_entry_progress;eassumption|
    eapply namespace_ptrace_has_no_entry_progress;eassumption|
    eapply namespace_clock_has_no_entry_progress;eassumption|
    eapply namespace_kill_has_no_entry_progress;eassumption|
    eapply namespace_sleep_has_no_entry_progress;eassumption].
Qed.

Theorem namespace_defined_run_projects ge cell start events target :
  namespace_entry_defined ge cell start ->namespace_steps ge cell(live start)events target ->
  exists actual,events=map(fun event=>namespace_process(process_entry event))actual /\
    entry_handoff_steps ge cell(live start)actual target.
Proof.
  intros DEFINED RUN;remember(live start)as initial eqn:INITIAL;revert start INITIAL DEFINED.
  induction RUN as[initial|initial event middle rest last STEP RUN IH];intros start INITIAL DEFINED;subst initial.
  - exists[];split;[reflexivity|constructor].
  - destruct(namespace_enabled_step_projects _ _ _ _ _
      (DEFINED[]start(entry_handoff_steps_nil _ _ _))STEP)as[actual[EVENT REAL]];subst event.
    destruct middle as[next|memory].
    + assert(TAIL:namespace_entry_defined ge cell next).
      { intros suffix current EXEC;apply(DEFINED(actual::suffix)current);econstructor;eassumption. }
      destruct(IH next eq_refl TAIL)as[suffix[EVENTS REST]];subst rest.
      exists(actual::suffix);split;[reflexivity|econstructor;eassumption].
    + destruct(namespace_dead_steps _ _ _ _ _ RUN)as[EVENTS TARGET];subst rest last.
      exists[actual];split;[reflexivity|econstructor;[exact REAL|constructor]].
Qed.

Theorem namespace_region_defined ge cell P R n start :
  handoff_region ge cell P R n start ->
  (forall endpoint,R endpoint->namespace_entry_defined ge cell endpoint) ->
  namespace_entry_defined ge cell start.
Proof.
  intros CERT LEAF events current RUN.
  destruct(handoff_region_execution_split _ _ _ _ _ _ CERT _ _ RUN)
    as[[MEMORY[COST[NOIMAGES RESIDUAL]]]|
      [prefix[endpoint[rest[EVENTS[COST[NOIMAGES[PREFIX[MEMORY[RESULT REST]]]]]]]]]].
  - destruct(RESIDUAL current eq_refl)as[remaining TAIL].
    inversion TAIL;subst.
    + apply(LEAF current H0 []current);constructor.
    + destruct H0 as[event[next[WAIT[IMAGE STEP]]]].
      exists event,(live next);split;[eapply namespace_entry_live_is_progress;eassumption|exact STEP].
  - eapply LEAF;[exact RESULT|exact REST].
Qed.
