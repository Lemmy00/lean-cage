(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.pid: Extract the actual admission and CG-close source intervals from the recorded grant. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
From LeanImport Require Import Lean.
Require Import Machine LibraryMachine ProcessEffects.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessJournal ProcessSourceClose ProcessOwnership ProcessPhysicalTrace.
From EntryNamespace Require Import NamespaceMachine NamespaceObjects NamespacePaths NamespaceMemory NamespaceCaller NamespaceChildResult
  NamespaceSourceFork NamespaceGrantInputs NamespaceParentEntry NamespaceParentSafety NamespaceAdmissionProjection
  NamespaceAdmissionGuarantee.
Import ListNotations.
Local Close Scope lean_scope.

Lemma admission_sources_constant events:
  Forall(fun event=>event=namespace_source_event)events ->events=repeat namespace_source_event(length events).
Proof.
  intro PURE;induction PURE;[reflexivity|];subst x;cbn;congruence.
Qed.

Lemma admission_parent_prelude_process events:
  Forall(fun event=>namespace_parent_prelude_event event=true)events ->
  exists originals,events=map namespace_process originals /\
    Forall(fun event=>process_quiet_event event=true)originals.
Proof.
  intro PRELUDE;induction PRELUDE as[|event events VALID REST IH].
  - exists[];split;constructor.
  - destruct IH as[originals[EVENTS QUIET]].
    destruct event;cbn[namespace_parent_prelude_event]in VALID;try discriminate.
    exists(event::originals);split;[cbn;rewrite EVENTS;reflexivity|].
    constructor;[|exact QUIET].
    destruct event;cbn[namespace_parent_prelude_event]in VALID;try discriminate.
    destruct event;cbn[namespace_parent_prelude_event]in VALID;try discriminate.
    destruct event;cbn[namespace_parent_prelude_event]in VALID;try discriminate;try reflexivity.
    destruct ev;cbn[namespace_parent_prelude_event]in VALID;try discriminate;reflexivity.
Qed.

Record RecordedAdmissionSource operation groups scope first snapshot run
    (fork:ActualSourceFork run(task_pid(fork_child snapshot)))
    (input:ParentPreparedInput scope first(source_fork_parent _ _ fork))
    owner child program channel ticks start read_offset read_tick
    (recorded:RecordedForkAdmission operation groups scope first snapshot run fork input owner child program channel
      ticks start read_offset read_tick):Type:={
  admission_source_prefix:list namespace_event;
  admission_source_events:list process_event;
  admission_source_after:mem;
  admission_close_guard:nat;
  admission_close_callback:list namespace_event;
  admission_close_after:mem;
  admission_source_suffix:list namespace_event;
  admission_close_waits:nat;
  admission_close_reply:close_reply;
  admission_close_zero:close_value admission_close_reply=Int.zero;
  admission_close_ordinal:nat;
  admission_source_full:source_events run=admission_source_prefix++map namespace_process admission_source_events++
    (repeat namespace_source_event admission_close_guard++admission_close_callback)++admission_source_suffix;
  admission_source_prefix_exact:admission_source_prefix=source_fork_common _ _ fork++
    [namespace_forked(task_pid(fork_child snapshot))]++recorded_finish_prefix recorded++recorded_setup_prefix recorded++
    repeat namespace_source_event 15;
  admission_source_run:process_steps ProcessGlobalCalls.caller_ge(scope_cell scope)
    (live(Callstate(Internal f_admit_child)
      [Vint(task_pid(fork_child snapshot));Vint(prepared_cgroup_fd input);Vptr(prepared_status_cell input)Ptrofs.zero]
      Kstop(recorded_ready recorded)))admission_source_events
    (live(Returnstate(Vint Int.zero)Kstop admission_source_after));
  admission_close_run:namespace_steps ProcessGlobalCalls.caller_ge(scope_cell scope)
    (live(Callstate close_definition[Vint(prepared_cgroup_fd input)]Kstop admission_source_after))admission_close_callback
    (live(Returnstate(Vint Int.zero)Kstop admission_close_after));
  admission_close_callback_exact:admission_close_callback=
    repeat(namespace_process(process_entry(entry_library library_wait)))admission_close_waits++
    [namespace_process(process_entry(entry_library(close_returned(prepared_cgroup_fd input)admission_close_reply)))];
  admission_close_selected:nth_error(source_events run)admission_close_ordinal=
    Some(namespace_process(process_entry(entry_library(close_returned(prepared_cgroup_fd input)admission_close_reply))));
  admission_close_ordinal_exact:admission_close_ordinal=(length admission_source_prefix+
    length admission_source_events+admission_close_guard+admission_close_waits)%nat;
  admission_close_end:S admission_close_ordinal=(length admission_source_prefix+
    length admission_source_events+admission_close_guard+length admission_close_callback)%nat;
  admission_close_before_resume:(admission_close_ordinal<recorded_source_resume recorded)%nat
}.

Arguments admission_source_prefix {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick recorded} _.
Arguments admission_source_events {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick recorded} _.
Arguments admission_source_after {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick recorded} _.
Arguments admission_close_guard {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick recorded} _.
Arguments admission_close_callback {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick recorded} _.
Arguments admission_close_after {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick recorded} _.
Arguments admission_source_suffix {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick recorded} _.
Arguments admission_close_waits {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick recorded} _.
Arguments admission_close_reply {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick recorded} _.
Arguments admission_close_zero {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick recorded} _.
Arguments admission_close_ordinal {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick recorded} _.
Arguments admission_source_full {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick recorded} _.
Arguments admission_source_prefix_exact {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick recorded} _.
Arguments admission_source_run {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick recorded} _.
Arguments admission_close_run {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick recorded} _.
Arguments admission_close_callback_exact {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick recorded} _.
Arguments admission_close_selected {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick recorded} _.
Arguments admission_close_ordinal_exact {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick recorded} _.
Arguments admission_close_end {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick recorded} _.
Arguments admission_close_before_resume {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick recorded} _.

Theorem recorded_grant_actual_admission_source operation groups scope first snapshot run
    (fork:ActualSourceFork run(task_pid(fork_child snapshot)))
    (input:ParentPreparedInput scope first(source_fork_parent _ _ fork))
    owner child program channel ticks start read_offset read_tick
    (recorded:RecordedForkAdmission operation groups scope first snapshot run fork input owner child program channel
      ticks start read_offset read_tick):
  inhabited(RecordedAdmissionSource operation groups scope first snapshot run fork input owner child program channel
    ticks start read_offset read_tick recorded).
Proof.
  pose proof(recorded_parent_authorized recorded)as AUTHORIZED.
  remember(recorded_grant_prefix recorded)as grant eqn:GRANT in AUTHORIZED.
  destruct AUTHORIZED as[first_close before_result before_clock before_publication publication_call publication_guard
    admit_events close_events result_events clock_events publication_events admitted closed forgotten constructed copied
    clocked published result milliseconds FIRST_CLOSE PURE_RESULT PURE_CLOCK PURE_PUBLICATION PURE_CALL PURE_GUARD
    ADMIT CLOSE FORGET RESULT COPY CLOCK NONZERO ELAPSED SEND].
  destruct(actual_namespace_admission_projects _ _ _ _ _ ADMIT)as[actual[ADMIT_EVENTS ACTUAL]].
  destruct(source_namespace_close_events _ _ _ _ _ _ _ CLOSE)as[waits[reply[CLOSE_EVENTS RETURNED]]].
  assert(ZERO:close_value reply=Int.zero)by(inversion RETURNED;reflexivity).
  set(prefix:=source_fork_common _ _ fork++[namespace_forked(task_pid(fork_child snapshot))]++
    recorded_finish_prefix recorded++recorded_setup_prefix recorded++repeat namespace_source_event 15).
  set(suffix:=before_result++result_events++before_clock++clock_events++before_publication++publication_call++
    publication_events++publication_guard++repeat namespace_source_event 5++recorded_release_prefix recorded++
    skipn(recorded_source_ordinal recorded-S(length(source_fork_common _ _ fork)))(source_fork_body _ _ fork)).
  assert(BODY:source_fork_body _ _ fork=recorded_finish_prefix recorded++recorded_setup_prefix recorded++
    recorded_grant_prefix recorded++recorded_release_prefix recorded++
    skipn(recorded_source_ordinal recorded-S(length(source_fork_common _ _ fork)))(source_fork_body _ _ fork)).
  { pose proof(firstn_skipn(recorded_source_ordinal recorded-S(length(source_fork_common _ _ fork)))
      (source_fork_body _ _ fork))as WHOLE.
    rewrite(recorded_source_order recorded)in WHOLE;repeat rewrite <-app_assoc in WHOLE;exact(eq_sym WHOLE). }
  assert(EVENTS:source_events run=prefix++map namespace_process actual++
    (repeat namespace_source_event(length first_close)++close_events)++suffix).
  { rewrite(source_fork_events _ _ fork),BODY,<-GRANT;unfold prefix,suffix.
    rewrite ADMIT_EVENTS,(admission_sources_constant _ FIRST_CLOSE).
    rewrite repeat_length.
    repeat rewrite <-app_assoc;reflexivity. }
  set(ordinal:=(length prefix+length actual+length first_close+waits)%nat).
  assert(SELECTED:nth_error(source_events run)ordinal=
    Some(namespace_process(process_entry(entry_library(close_returned(prepared_cgroup_fd input)reply))))).
  { rewrite EVENTS;unfold ordinal.
    rewrite nth_error_app2 by lia.
    replace(length prefix+length actual+length first_close+waits-length prefix)%nat
      with(length actual+length first_close+waits)%nat by lia.
    rewrite nth_error_app2 by(rewrite length_map;lia).
    rewrite length_map.
    replace(length actual+length first_close+waits-length actual)%nat with(length first_close+waits)%nat by lia.
    rewrite nth_error_app1 by(rewrite length_app,repeat_length,CLOSE_EVENTS,length_app,repeat_length;cbn;lia).
    rewrite nth_error_app2 by(rewrite repeat_length;lia).
    rewrite repeat_length.
    replace(length first_close+waits-length first_close)%nat with waits by lia.
    rewrite CLOSE_EVENTS,nth_error_app2 by(rewrite repeat_length;lia).
    rewrite repeat_length,Nat.sub_diag;reflexivity. }
  assert(END:S ordinal=(length prefix+length actual+length first_close+length close_events)%nat).
  { rewrite CLOSE_EVENTS,length_app,repeat_length;cbn;unfold ordinal;lia. }
  assert(BEFORE:(ordinal<recorded_source_resume recorded)%nat).
  { pose proof(recorded_grant_before_resume recorded)as ORDER.
    rewrite <-GRANT in ORDER.
    pose proof(f_equal(@length namespace_event)ADMIT_EVENTS)as ADMIT_LENGTH.
    rewrite length_map in ADMIT_LENGTH.
    pose proof(f_equal(@length namespace_event)CLOSE_EVENTS)as CLOSE_LENGTH.
    rewrite length_app,repeat_length in CLOSE_LENGTH;cbn in CLOSE_LENGTH.
    unfold ordinal,prefix;repeat rewrite length_app;rewrite repeat_length;cbn.
    repeat rewrite length_app in ORDER;rewrite repeat_length in ORDER.
    lia. }
  constructor;refine{|admission_source_prefix:=prefix;admission_source_events:=actual;admission_source_after:=admitted;
    admission_close_guard:=length first_close;admission_close_callback:=close_events;admission_close_after:=closed;
    admission_source_suffix:=suffix;admission_close_waits:=waits;admission_close_reply:=reply;
    admission_close_ordinal:=ordinal|};try assumption;reflexivity.
Qed.
