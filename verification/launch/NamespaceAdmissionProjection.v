(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Actual namespace callbacks project to their supported primitive machine. *)
From Stdlib Require Import ZArith List Bool String.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine LibraryMachine.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessGlobalCalls ProcessCaller.
From EntryNamespace Require Import NamespaceMachine NamespaceClosure.
Import ListNotations.
Local Open Scope string_scope.

Definition closure_external_named names(fd:Clight.fundef):=match fd with
  |External(EF_external name _) _ _ _=>existsb(String.eqb name)names|_=>false end.
Definition closure_excludes ids names:=forallb(fun id=>match closure_lookup id with
  |Some fd=>negb(closure_external_named names fd)|None=>false end)ids.
Definition namespace_primitive_names:=
  ["socketpair";"entry_duplicate_above";"entry_signal_mask";"entry_signal_default";"fork"].

Lemma closure_excluded_function ids names fd:
  closure_excludes ids names=true ->closure_function ids fd ->closure_external_named names fd=false.
Proof.
  intros EXCLUDED[id[MEMBER LOOKUP]];unfold closure_excludes in EXCLUDED.
  apply forallb_forall with(x:=id)in EXCLUDED;[|exact MEMBER].
  rewrite LOOKUP in EXCLUDED;apply Bool.negb_true_iff;exact EXCLUDED.
Qed.

Definition callback_library_exclusions:=List.app namespace_primitive_names
  ["waitpid";"entry_ptrace4";"clock_gettime";"entry_decimal";"entry_descriptor_flags";"execve";"kill";"usleep"].

Ltac closure_reject_extra :=
  match goal with GOOD:closure_machine ?ids(live(Callstate ?fd _ _ _)),
    EXCLUDED:closure_excludes ?ids callback_library_exclusions=true|-_=>
      destruct GOOD as[GLOBALS[FUNCTION CONT]];
      pose proof(closure_excluded_function ids callback_library_exclusions fd EXCLUDED FUNCTION)as IMPOSSIBLE;
      change(true=false)in IMPOSSIBLE;discriminate
  end.

Theorem closure_namespace_library_step ids cell state event target:
  closure_excludes ids callback_library_exclusions=true ->closure_machine ids(live state) ->
  namespace_step caller_ge cell(live state)event target ->
  exists actual,event=namespace_process(process_entry(entry_library actual)) /\
    library_step caller_ge cell(live state)actual target.
Proof.
  intros EXCLUDED GOOD STEP;inversion STEP;subst.
  all:try match goal with PROCESS:process_step _ _ _ _ _|-_=>inversion PROCESS;subst;clear PROCESS end.
  all:try match goal with ENTRY:entry_handoff_step _ _ _ _ _|-_=>inversion ENTRY;subst;clear ENTRY end.
  all:try solve[eexists;split;[reflexivity|eassumption]].
  all:try match goal with READY:namespace_ready _|-_=>inversion READY;subst end.
  all:closure_reject_extra.
Qed.

Theorem closure_namespace_runs_are_library_runs ids cell before events after:
  closure_profile ids=true ->closure_excludes ids callback_library_exclusions=true ->
  closure_machine ids before ->namespace_steps caller_ge cell before events after ->
  exists actual,events=map(fun event=>namespace_process(process_entry(entry_library event)))actual /\
    library_steps caller_ge cell before actual after.
Proof.
  intros PROFILE EXCLUDED GOOD RUN;revert GOOD.
  induction RUN as[initial|initial event middle rest last STEP RUN IH];intros GOOD.
  - exists[];split;[reflexivity|constructor].
  - destruct initial as[state|memory].
    + destruct(closure_namespace_library_step _ _ _ _ _ EXCLUDED GOOD STEP)
        as[original[EVENT REAL]];subst event.
      assert(NEXT:closure_machine ids middle)by(eapply closure_namespace_step;eassumption).
      destruct(IH NEXT)as[actual[EVENTS TAIL]];subst rest.
      exists(original::actual);split;[reflexivity|econstructor;eassumption].
    + exfalso;eapply namespace_dead_cannot_resume;exact STEP.
Qed.

Definition clock_call_profile:=[_now_ms;_clock_gettime].
Theorem clock_call_profile_checked:closure_profile clock_call_profile=true.
Proof. vm_compute;reflexivity. Qed.
Theorem clock_call_profile_no_namespace:closure_excludes clock_call_profile namespace_primitive_names=true.
Proof. vm_compute;reflexivity. Qed.

Definition sender_call_profile:=
  [_send_frame;_put32;_put64;_write_all;_fault;_error_number;_write;___errno_location;_memcpy].
Theorem sender_call_profile_checked:closure_profile sender_call_profile=true.
Proof. vm_compute;reflexivity. Qed.
Theorem sender_call_profile_no_extras:closure_excludes sender_call_profile callback_library_exclusions=true.
Proof. vm_compute;reflexivity. Qed.

Theorem closure_excludes_namespace_ready ids state:
  closure_excludes ids namespace_primitive_names=true ->closure_control ids state ->~namespace_ready state.
Proof.
  intros EXCLUDED CONTROL READY;inversion READY;subst;
    cbn[closure_control]in CONTROL;destruct CONTROL as[FUNCTION CONT];
    pose proof(closure_excluded_function _ _ _ EXCLUDED FUNCTION)as OUTSIDE;
    change(true=false)in OUTSIDE;discriminate.
Qed.

Theorem closure_namespace_runs_are_process_runs ids cell before events after:
  closure_profile ids=true ->closure_excludes ids namespace_primitive_names=true ->
  closure_machine ids before ->namespace_steps caller_ge cell before events after ->
  exists actual,events=map namespace_process actual /\process_steps caller_ge cell before actual after.
Proof.
  intros PROFILE EXCLUDES GOOD RUN;revert GOOD.
  induction RUN as[initial|initial event middle rest last STEP RUN IH];intros GOOD.
  - exists[];split;[reflexivity|constructor].
  - destruct initial as[state|memory].
    + assert(OUTSIDE:~namespace_ready state).
      { eapply closure_excludes_namespace_ready;[exact EXCLUDES|exact(proj2 GOOD)]. }
      destruct(namespace_process_projection _ _ _ _ _ OUTSIDE STEP)as[original[EVENT REAL]];subst event.
      assert(NEXT:closure_machine ids middle)by(eapply closure_namespace_step;eassumption).
      destruct(IH NEXT)as[actual[EVENTS TAIL]];subst rest.
      exists(original::actual);split;[reflexivity|econstructor;eassumption].
    + exfalso;eapply namespace_dead_cannot_resume;exact STEP.
Qed.

Definition admission_call_profile:=
  [_admit_child;_number;_write_all;_error_number;_waitpid;_entry_ptrace4;_entry_decimal;_write;___errno_location].

Theorem admission_call_profile_checked:closure_profile admission_call_profile=true.
Proof. vm_compute;reflexivity. Qed.
Theorem admission_call_profile_no_namespace:closure_excludes admission_call_profile namespace_primitive_names=true.
Proof. vm_compute;reflexivity. Qed.

Lemma admission_call_profile_start arguments memory:
  closure_state admission_call_profile(Callstate(Internal f_admit_child)arguments Kstop memory).
Proof.
  split.
  - split;[vm_compute;reflexivity|exact I].
  - split.
    + exists _admit_child;split;[left;reflexivity|vm_compute;reflexivity].
    + exact I.
Qed.

Theorem actual_namespace_admission_projects cell arguments memory events target:
  namespace_steps caller_ge cell(live(Callstate(Internal f_admit_child)arguments Kstop memory))events target ->
  exists actual,events=map namespace_process actual /\
    process_steps caller_ge cell(live(Callstate(Internal f_admit_child)arguments Kstop memory))actual target.
Proof.
  intro RUN;eapply closure_namespace_runs_are_process_runs;
    [exact admission_call_profile_checked|exact admission_call_profile_no_namespace|
     apply admission_call_profile_start|exact RUN].
Qed.

Lemma closure_start_named_call ids id fn arguments memory:
  In id ids ->closure_lookup id=Some(Internal fn) ->
  caller_vars_safe fn=true ->
  closure_state ids(Callstate(Internal fn)arguments Kstop memory).
Proof.
  intros MEMBER LOOKUP VARIABLES;split.
  - split;[exact VARIABLES|exact I].
  - split;[exists id;split;assumption|exact I].
Qed.

Theorem actual_namespace_clock_projects cell arguments memory events target:
  namespace_steps caller_ge cell(live(Callstate(Internal f_now_ms)arguments Kstop memory))events target ->
  exists actual,events=map namespace_process actual /\
    process_steps caller_ge cell(live(Callstate(Internal f_now_ms)arguments Kstop memory))actual target.
Proof.
  intro RUN;eapply closure_namespace_runs_are_process_runs;
    [exact clock_call_profile_checked|exact clock_call_profile_no_namespace| |exact RUN].
  eapply closure_start_named_call with(id:=_now_ms);
    [left;reflexivity|vm_compute;reflexivity|vm_compute;reflexivity].
Qed.

Theorem actual_namespace_sender_projects cell arguments memory events target:
  namespace_steps caller_ge cell(live(Callstate(Internal f_send_frame)arguments Kstop memory))events target ->
  exists actual,events=map(fun event=>namespace_process(process_entry(entry_library event)))actual /\
    library_steps caller_ge cell(live(Callstate(Internal f_send_frame)arguments Kstop memory))actual target.
Proof.
  intro RUN;eapply closure_namespace_runs_are_library_runs;
    [exact sender_call_profile_checked|exact sender_call_profile_no_extras| |exact RUN].
  eapply closure_start_named_call with(id:=_send_frame);
    [left;reflexivity|vm_compute;reflexivity|vm_compute;reflexivity].
Qed.
