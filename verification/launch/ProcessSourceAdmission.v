(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.pid: Actual successful admission establishes scope in the same source world. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers Values Memory Clight Ctypes Ctypesdefs.
From LeanImport Require Import Lean.
Require Import Machine LibraryMachine.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessAllocation ProcessStructure ProcessImport ProcessJournal
  ProcessOwnership ProcessPhysicalTrace ProcessFileTrace
  ProcessAdmissionPhysical ProcessSourceRecording ProcessSourceTables ProcessSourceWorlds.
From EntryNamespace Require Import NamespaceMachine NamespaceObjects NamespacePhysical.
Import ListNotations.
Local Close Scope lean_scope.
Local Open Scope Z_scope.

Lemma source_selected_interval(A:Type)(prefix events suffix:list A):
  firstn(length events)(skipn(length prefix)(prefix++events++suffix))=events.
Proof.
  rewrite skipn_app,skipn_all,Nat.sub_diag;cbn.
  rewrite firstn_app,firstn_all,Nat.sub_diag;cbn;apply app_nil_r.
Qed.

Theorem source_process_scope_to_close_checkpoint operation(linux:LinuxProcessContract operation)
    groups child runs tracked other parent cursor worlds before prefix close_tick final final_worlds after
    run ordinal fd reply group:
  SourceOtherContract other groups parent(physical_identity_task child) ->
  (forall actual,nth_error runs tracked=Some actual ->physical_identity_task(source_actor actual)=parent) ->
  SourceProcessSchedule operation groups child runs tracked other cursor worlds before(prefix++[close_tick])
    final final_worlds after ->
  SourceOtherAuthority groups tracked(prefix++[close_tick]) ->
  OwnsUnreaped before parent(physical_identity_task child) ->
  owned_cgroup(process_tasks before(physical_identity_task child))=Some group ->
  Forall(fun event=>process_quiet_event event=true)
    (source_program_process_events runs tracked(prefix++[close_tick])) ->
  LeanCage_Entry_CallerPhysical_Tick_source close_tick=source_reference tracked ordinal ->
  nth_error runs tracked=Some run ->nth_error(source_events run)ordinal=
    Some(namespace_process(process_entry(entry_library(close_returned fd reply)))) ->
  Lean.eq
    (LeanCage_Entry_CallerPhysical_Context_cgroup(LeanCage_Entry_CallerPhysical_Tick_after close_tick))
    (ProcessImport.Option_some_inst1 Lean.Nat(Nat_of_nat group)).
Proof.
  intros CONTRACT ACTOR RUN AUTHORITY OWNER GROUP QUIET REFERENCE PROGRAM EVENT.
  destruct(source_process_schedule_scope operation linux groups child runs tracked other parent cursor worlds before
    (prefix++[close_tick])final final_worlds after group CONTRACT ACTOR RUN OWNER GROUP AUTHORITY QUIET)
    as[FINAL_OWNER FINAL_GROUP].
  destruct(source_process_schedule_split _ _ _ _ _ _ _ _ _ _ _ _ _ _ RUN)
    as[middle[middle_worlds[boundary[PREFIX SUFFIX]]]].
  inversion SUFFIX as[|a b c d next next_worlds observed rest e f g STEP TAIL];subst.
  inversion TAIL;subst.
  destruct(source_process_step_selected operation groups child runs tracked other middle middle_worlds boundary
    close_tick final final_worlds after ordinal STEP REFERENCE)
    as[actual[original[snapshot[ACTUAL[ORIGINAL[PRIMITIVE[BEFORE[AFTER VIEW]]]]]]]].
  assert(ACTUAL_RUN:actual=run)by congruence;subst actual.
  assert(RESULT:LeanCage_Entry_CallerPhysical_Context_cgroup
    (LeanCage_Entry_CallerPhysical_Tick_after close_tick)=
    ProcessImport.Option_some_inst1 Lean.Nat(Nat_of_nat group)).
  { eapply source_view_has_group;[eapply source_primitive_after;exact PRIMITIVE|].
    rewrite AFTER;exact FINAL_GROUP. }
  rewrite RESULT;constructor.
Qed.

Lemma source_parent_events_exact events:
  flat_map(fun event=>match event with namespace_process original=>[original]|_=>[]end)
    (map namespace_process events)=events.
Proof. induction events;cbn;congruence. Qed.

Theorem source_process_schedule_event_slice operation groups child runs tracked other cursor worlds before ticks
    final final_worlds after run prefix events suffix:
  SourceProcessSchedule operation groups child runs tracked other cursor worlds before ticks final final_worlds after ->
  nth_error runs tracked=Some run ->source_events run=prefix++map namespace_process events++suffix ->
  cursor tracked=length prefix ->final tracked=(length prefix+length events)%nat ->
  source_program_process_events runs tracked ticks=events.
Proof.
  intros RUN PROGRAM EVENTS START FINISH.
  unfold source_program_process_events.
  rewrite(source_table_schedule_program_events _ _ _ _ _ _ _ _ _
    (source_process_schedule_tables _ _ _ _ _ _ _ _ _ _ _ _ _ RUN)PROGRAM).
  rewrite START,FINISH,EVENTS.
  replace(length prefix+length events-length prefix)%nat with(length events)by lia.
  rewrite <-(length_map namespace_process events)at 1.
  rewrite source_selected_interval;apply source_parent_events_exact.
Qed.

Theorem source_process_admission_return_scope operation(linux:LinuxProcessContract operation)
    groups child runs tracked other parent cursor worlds before ticks final final_worlds after
    cell before_memory events after_memory cgroup group status offset:
  SourceOtherContract other groups parent(physical_identity_task child) ->
  (forall run,nth_error runs tracked=Some run ->physical_identity_task(source_actor run)=parent) ->
  SourceProcessSchedule operation groups child runs tracked other cursor worlds before ticks final final_worlds after ->
  SourceOtherAuthority groups tracked ticks ->
  source_program_process_events runs tracked ticks=events ->
  1<=Int.signed(task_pid(physical_identity_task child)) ->
  status<>tls_block cell ->Mem.valid_block before_memory(tls_block cell) ->
  OwnsUnreaped before parent(physical_identity_task child) ->
  process_cgroup_files before parent cgroup=Some group ->
  process_steps admission_ge cell
    (live(Callstate(Internal f_admit_child)
      [Vint(task_pid(physical_identity_task child));Vint cgroup;Vptr status offset]Kstop before_memory))events
    (live(Returnstate(Vint Int.zero)Kstop after_memory)) ->
  OwnsUnreaped after parent(physical_identity_task child) /\
    owned_cgroup(process_tasks after(physical_identity_task child))=Some group.
Proof.
  intros CONTRACT ACTOR RUN AUTHORITY EVENTS POSITIVE SEPARATE ERRNO OWNER FILE SOURCE.
  pose proof(admission_actual_file_frames_from_live_tls _ _ _ _ _ _ _ _ POSITIVE SEPARATE ERRNO SOURCE)as FILES.
  assert(NONREAP:Forall(fun event=>process_nonreaping event=true)
    (source_program_process_events runs tracked ticks)).
  { rewrite EVENTS;apply Forall_forall;intros event MEMBER.
    apply Forall_forall with(x:=event)in FILES;[apply file_event_retains_lease;exact FILES|exact MEMBER]. }
  destruct(source_process_schedule_projects operation linux groups child runs tracked other parent cursor worlds before
    ticks final final_worlds after CONTRACT ACTOR RUN OWNER AUTHORITY NONREAP)
    as[boundary[STEPS[INTERFERENCE FINAL_OWNER]]].
  rewrite EVENTS in STEPS.
  destruct(actual_admission_return_scope_from_live_tls _ linux _ _ _ _ _ _ _ _ _ _ _ _
    POSITIVE SEPARATE ERRNO OWNER FILE SOURCE STEPS)as[BOUND_OWNER GROUP].
  split;[exact FINAL_OWNER|].
  rewrite(interference_owned_scope _ _ _ _ BOUND_OWNER INTERFERENCE);exact GROUP.
Qed.

Theorem source_process_admission_from_source_slice operation(linux:LinuxProcessContract operation)
    groups child runs tracked other parent cursor worlds before ticks final final_worlds after run prefix suffix
    cell before_memory events after_memory cgroup group status offset:
  SourceOtherContract other groups parent(physical_identity_task child) ->
  (forall actual,nth_error runs tracked=Some actual ->physical_identity_task(source_actor actual)=parent) ->
  SourceProcessSchedule operation groups child runs tracked other cursor worlds before ticks final final_worlds after ->
  SourceOtherAuthority groups tracked ticks ->nth_error runs tracked=Some run ->
  source_events run=prefix++map namespace_process events++suffix ->
  cursor tracked=length prefix ->final tracked=(length prefix+length events)%nat ->
  1<=Int.signed(task_pid(physical_identity_task child)) ->
  status<>tls_block cell ->Mem.valid_block before_memory(tls_block cell) ->
  OwnsUnreaped before parent(physical_identity_task child) ->
  process_cgroup_files before parent cgroup=Some group ->
  process_steps admission_ge cell
    (live(Callstate(Internal f_admit_child)
      [Vint(task_pid(physical_identity_task child));Vint cgroup;Vptr status offset]Kstop before_memory))events
    (live(Returnstate(Vint Int.zero)Kstop after_memory)) ->
  OwnsUnreaped after parent(physical_identity_task child) /\
    owned_cgroup(process_tasks after(physical_identity_task child))=Some group.
Proof.
  intros CONTRACT ACTOR RUN AUTHORITY PROGRAM EVENTS START FINISH POSITIVE SEPARATE ERRNO OWNER FILE SOURCE.
  eapply source_process_admission_return_scope;try eassumption.
  eapply source_process_schedule_event_slice;eassumption.
Qed.

(* The options snapshot comes from the actual successful helper, its exact
   source slice and its fork-owned nonreaping prefix in this same journal. *)
Record SourceOptionsAt owner child tracked run ticks position tick ordinal:Prop:={
  source_options_selected:nth_error ticks position=Some tick;
  source_options_reference:LeanCage_Entry_CallerPhysical_Tick_source tick=source_reference tracked ordinal;
  source_options_event:nth_error(source_events run)ordinal=Some(namespace_process(process_traced(Int.repr 16896)
    (task_pid(physical_identity_task child))(Vlong Int64.zero)(Vlong(Int64.repr 1048592))Int64.zero));
  source_options_tracer:Lean.eq
    (LeanCage_Entry_CallerPhysical_Context_tracer(LeanCage_Entry_CallerPhysical_Tick_before tick))
    (ProcessImport.Option_some_inst1 LeanCage_Entry_ProcessIdentity owner)
}.

Theorem source_process_admission_options_checkpoint operation(linux:LinuxProcessContract operation)
    groups owner child runs tracked other cursor worlds before ticks final final_worlds after run prefix suffix
    cell before_memory events after_memory cgroup group status offset:
  SourceOtherContract other groups(physical_identity_task owner)(physical_identity_task child) ->
  (forall actual,nth_error runs tracked=Some actual ->source_actor actual=owner) ->
  SourceProcessSchedule operation groups child runs tracked other cursor worlds before ticks final final_worlds after ->
  SourceOtherAuthority groups tracked ticks ->nth_error runs tracked=Some run ->
  source_events run=prefix++map namespace_process events++suffix ->
  cursor tracked=length prefix ->final tracked=(length prefix+length events)%nat ->
  status<>tls_block cell ->Mem.valid_block before_memory(tls_block cell) ->
  OwnsUnreaped before(physical_identity_task owner)(physical_identity_task child) ->
  process_cgroup_files before(physical_identity_task owner)cgroup=Some group ->
  process_steps admission_ge cell
    (live(Callstate(Internal f_admit_child)
      [Vint(task_pid(physical_identity_task child));Vint cgroup;Vptr status offset]Kstop before_memory))events
    (live(Returnstate(Vint Int.zero)Kstop after_memory)) ->
  exists position tick ordinal,SourceOptionsAt owner child tracked run ticks position tick ordinal.
Proof.
  intros CONTRACT ACTOR RUN AUTHORITY PROGRAM SOURCE_EVENTS START FINISH SEPARATE TLS OWNER FILE SOURCE.
  assert(POSITIVE:1<=Int.signed(task_pid(physical_identity_task child))).
  { rewrite physical_identity_task_pid;exact(proj1(physical_identity_pid_range child)). }
  assert(TASK_ACTOR:forall actual,nth_error runs tracked=Some actual ->
    physical_identity_task(source_actor actual)=physical_identity_task owner).
  { intros actual PRESENT;rewrite(ACTOR _ PRESENT);reflexivity. }
  assert(EVENTS:source_program_process_events runs tracked ticks=events).
  { eapply source_process_schedule_event_slice;eassumption. }
  pose proof(admission_actual_file_frames_from_live_tls _ _ _ _ _ _ _ _ POSITIVE SEPARATE TLS SOURCE)as FILES.
  assert(NONREAP:Forall(fun event=>process_nonreaping event=true)(source_program_process_events runs tracked ticks)).
  { rewrite EVENTS;apply Forall_forall;intros event MEMBER.
    apply Forall_forall with(x:=event)in FILES;[apply file_event_retains_lease;exact FILES|exact MEMBER]. }
  destruct(source_process_schedule_projects operation linux groups child runs tracked other
    (physical_identity_task owner)cursor worlds before ticks final final_worlds after
    CONTRACT TASK_ACTOR RUN OWNER AUTHORITY NONREAP)as[boundary[STEPS[INTERFERENCE FINAL_OWNER]]].
  rewrite EVENTS in STEPS.
  pose proof(actual_admission_establishes_scope_from_live_tls operation linux cell before_memory
    (physical_identity_task owner)(physical_identity_task child)before events after_memory boundary cgroup group status offset
    POSITIVE SEPARATE TLS OWNER FILE SOURCE STEPS)as SNAPSHOTS.
  destruct SNAPSHOTS as[locals count bytes error word initial between tail
    write_boundary write_observed placed options_boundary options_observed configured
    CANONICAL STOP SIGNAL STOP_EVENT ORDER PREFIX WRITE_INTERFERENCE WRITE_OWNER WRITE_FILE WRITE_STEP
    PLACED_OWNER PLACED_GROUP BETWEEN OPTIONS_INTERFERENCE OPTIONS_STEP STOPPED OPTIONS GROUP QUIET TAIL].
  set(optionEvent:=process_traced(Int.repr 16896)(task_pid(physical_identity_task child))(Vlong Int64.zero)
    (Vlong(Int64.repr 1048592))Int64.zero).
  set(index:=(length initial+1+length between)%nat).
  assert(OPTION_AT:nth_error events index=Some optionEvent).
  { rewrite ORDER;unfold index;rewrite nth_error_app2 by lia.
    replace(length initial+1+length between-length initial)%nat with(S(length between))by lia.
    cbn;rewrite nth_error_app2 by lia;rewrite Nat.sub_diag;reflexivity. }
  assert(INDEX:(index<length events)%nat).
  { apply nth_error_Some;rewrite OPTION_AT;discriminate. }
  set(ordinal:=(length prefix+index)%nat).
  assert(ORIGINAL:nth_error(source_events run)ordinal=Some(namespace_process optionEvent)).
  { rewrite SOURCE_EVENTS;unfold ordinal;rewrite nth_error_app2 by lia.
    replace(length prefix+index-length prefix)%nat with index by lia.
    rewrite nth_error_app1 by(rewrite length_map;exact INDEX).
    rewrite nth_error_map,OPTION_AT;reflexivity. }
  assert(BOUNDS:(cursor tracked<=ordinal<final tracked)%nat)by(unfold ordinal;rewrite START,FINISH;lia).
  pose proof(source_table_schedule_erases _ _ _ _ _ _ _
    (source_process_schedule_tables _ _ _ _ _ _ _ _ _ _ _ _ _ RUN))as PRIMITIVES.
  destruct(source_event_schedule_covers _ _ _ _ _ _ _ _ _ PRIMITIVES BOUNDS PROGRAM ORIGINAL)
    as[position[tick[snapshot[SELECTED[REFERENCE PRIMITIVE]]]]].
  pose proof SELECTED as POSITION;apply nth_error_split in POSITION.
  destruct POSITION as[tick_prefix[tick_suffix[TICKS LENGTH]]].
  assert(RUN_SELECTED:SourceProcessSchedule operation groups child runs tracked other cursor worlds before
    (tick_prefix++tick::tick_suffix)final final_worlds after)by(rewrite <-TICKS;exact RUN).
  assert(AUTH_SELECTED:SourceOtherAuthority groups tracked(tick_prefix++tick::tick_suffix))
    by(rewrite <-TICKS;exact AUTHORITY).
  assert(LEASE_SELECTED:Forall(fun event=>process_nonreaping event=true)
    (source_program_process_events runs tracked(tick_prefix++tick::tick_suffix)))
    by(rewrite <-TICKS;exact NONREAP).
  destruct(source_process_selected_before_owner operation linux groups child runs tracked other
    (physical_identity_task owner)cursor worlds before tick_prefix tick tick_suffix final final_worlds after ordinal
    CONTRACT TASK_ACTOR RUN_SELECTED AUTH_SELECTED OWNER LEASE_SELECTED REFERENCE)
    as[actual[original[observed[ACTUAL[OBSERVED[REAL OWNED]]]]]].
  assert(ACTUAL_RUN:actual=run)by congruence;subst actual.
  assert(ACTUAL_EVENT:original=optionEvent)by congruence;subst original.
  rewrite(ACTOR _ PROGRAM)in REAL.
  exists position,tick,ordinal;constructor;[exact SELECTED|exact REFERENCE|exact ORIGINAL|].
  eapply recorded_source_options_before;[exact linux|exact REAL|reflexivity|exact OWNED].
Qed.
