(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.pid: The public scope consumer receives options and cgroup closure from one recorded launch. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
From LeanImport Require Import Lean.
Require Import IO Machine LibraryMachine ProcessEffects.
From EntryNative Require Import EntrySource NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessImport ProcessJournal ProcessOwnership ProcessPhysicalTrace
  ProcessSourceRecording ProcessSourceTables ProcessSourceWorlds ProcessSourceSlices ProcessSourceFiles
  ProcessSourceAdmission ProcessSourceCheckpoint ProcessSourceClose ProcessScope ProcessCgroupRecording.
From EntryNamespace Require Import NamespaceMachine NamespaceObjects NamespaceKernel NamespacePhysical NamespaceWorldTrace
  NamespacePaths NamespaceMemory NamespaceCaller NamespaceChildResult NamespaceSourceFork NamespaceGrantInputs
  NamespaceParentEntry NamespacePreludeFrames NamespaceAdmissionGuarantee NamespaceAdmissionSlices.
Import ListNotations.
Local Close Scope lean_scope.

Lemma application_source_authority_subset groups program before after:
  SourceOtherAuthority groups program after ->(forall tick,In tick before ->In tick after) ->
  SourceOtherAuthority groups program before.
Proof.
  intros AUTH INCLUDED;constructor;intros tick MEMBER OUTSIDE.
  - eapply source_other_quiet;[exact AUTH|apply INCLUDED;exact MEMBER|exact OUTSIDE].
  - eapply source_other_live;[exact AUTH|apply INCLUDED;exact MEMBER|exact OUTSIDE].
Qed.

Lemma application_prelude_quiet events:
  Forall(fun event=>process_quiet_event event=true)events ->Forall(fun event=>process_nonreaping event=true)events.
Proof.
  intro QUIET;apply Forall_forall;intros event MEMBER;apply Forall_forall with(x:=event)in QUIET;[|exact MEMBER].
  unfold process_quiet_event in QUIET;apply Bool.andb_true_iff in QUIET;exact(proj1 QUIET).
Qed.

Lemma application_source_exact_slice primitive runs cursor worlds ticks final final_worlds program run prefix events suffix:
  SourceTableSchedule primitive runs cursor worlds ticks final final_worlds ->nth_error runs program=Some run ->
  source_events run=prefix++events++suffix ->cursor program=length prefix ->
  final program=(length prefix+length events)%nat ->source_program_events runs program ticks=events.
Proof.
  intros RUN PROGRAM EVENTS START FINISH.
  rewrite(source_table_schedule_program_events _ _ _ _ _ _ _ _ _ RUN PROGRAM),START,FINISH,EVENTS.
  replace(length prefix+length events-length prefix)%nat with(length events)by lia;apply source_selected_interval.
Qed.

Lemma application_schedule_last_cursor operation groups child runs tracked other cursor worlds before prefix tick
    final final_worlds after ordinal:
  SourceProcessSchedule operation groups child runs tracked other cursor worlds before(prefix++[tick])final final_worlds after ->
  LeanCage_Entry_CallerPhysical_Tick_source tick=source_reference tracked ordinal ->final tracked=S ordinal.
Proof.
  intros RUN REFERENCE.
  destruct(source_process_schedule_split _ _ _ _ _ _ _ _ _ _ _ _ _ _ RUN)
    as[middle[middle_worlds[observed[PREFIX LAST]]]].
  inversion LAST as[|a b c d next next_worlds next_world rest e f g STEP TAIL];subst.
  inversion TAIL;subst.
  eapply source_cursor_selected;[eapply source_process_step_cursor;exact STEP|exact REFERENCE].
Qed.

Lemma application_empty_schedule_cursor operation groups child runs tracked other cursor worlds before
    final final_worlds after:
  SourceProcessSchedule operation groups child runs tracked other cursor worlds before[]final final_worlds after ->
  final=cursor.
Proof. intro RUN;inversion RUN;reflexivity. Qed.

Lemma application_last_suffix(A:Type)(prefix whole suffix:list A)value:
  prefix++[value]=whole++suffix ->suffix<>[] ->exists before,suffix=before++[value].
Proof.
  intros SAME NONEMPTY;destruct suffix using rev_ind;[contradiction|].
  rewrite app_assoc in SAME;apply app_inj_tail in SAME as[PREFIX LAST];subst x.
  exists suffix;reflexivity.
Qed.

Record ApplicationPositions(owner child:LeanCage_Entry_ProcessIdentity)(program:nat)(run:CallerSourceRun)(cgroup_fd:int)
    (ticks:list LeanCage_Entry_CallerPhysical_Tick)
    (start read_offset group resume_offset:nat):Type:={
  application_options_offset:nat;
  application_options_tick:LeanCage_Entry_CallerPhysical_Tick;
  application_close_offset:nat;
  application_close_tick:LeanCage_Entry_CallerPhysical_Tick;
  application_close_ordinal:nat;
  application_close_reply:close_reply;
  application_close_reference:LeanCage_Entry_CallerPhysical_Tick_source application_close_tick=
    source_reference program application_close_ordinal;
  application_close_source:nth_error(source_events run)application_close_ordinal=
    Some(namespace_process(process_entry(entry_library(close_returned cgroup_fd application_close_reply))));
  application_close_zero:close_value application_close_reply=Int.zero;
  application_options_selected:nth_error ticks application_options_offset=Some application_options_tick;
  application_close_selected:nth_error ticks application_close_offset=Some application_close_tick;
  application_options_at:LeanCage_Entry_CallerPhysical_TickAt(tick_values ticks)(Nat_of_nat application_options_offset)
    application_options_tick;
  application_close_at:LeanCage_Entry_CallerPhysical_TickAt(tick_values ticks)(Nat_of_nat application_close_offset)
    application_close_tick;
  application_options_tracer:Lean.eq
    (LeanCage_Entry_CallerPhysical_Context_tracer(LeanCage_Entry_CallerPhysical_Tick_before application_options_tick))
    (ProcessImport.Option_some_inst1 LeanCage_Entry_ProcessIdentity owner);
  application_close_group:Lean.eq
    (LeanCage_Entry_CallerPhysical_Context_cgroup(LeanCage_Entry_CallerPhysical_Tick_after application_close_tick))
    (ProcessImport.Option_some_inst1 Lean.Nat(Nat_of_nat group));
  application_options_before_close:(application_options_offset<=application_close_offset)%nat;
  application_close_before_resume:(application_close_offset<resume_offset)%nat;
  application_close_before_read:(application_close_offset<read_offset)%nat
}.

Arguments application_options_offset {owner child program run cgroup_fd ticks start read_offset group resume_offset} _.
Arguments application_options_tick {owner child program run cgroup_fd ticks start read_offset group resume_offset} _.
Arguments application_close_offset {owner child program run cgroup_fd ticks start read_offset group resume_offset} _.
Arguments application_close_tick {owner child program run cgroup_fd ticks start read_offset group resume_offset} _.
Arguments application_close_ordinal {owner child program run cgroup_fd ticks start read_offset group resume_offset} _.
Arguments application_close_reply {owner child program run cgroup_fd ticks start read_offset group resume_offset} _.
Arguments application_close_reference {owner child program run cgroup_fd ticks start read_offset group resume_offset} _.
Arguments application_close_source {owner child program run cgroup_fd ticks start read_offset group resume_offset} _.
Arguments application_close_zero {owner child program run cgroup_fd ticks start read_offset group resume_offset} _.
Arguments application_options_selected {owner child program run cgroup_fd ticks start read_offset group resume_offset} _.
Arguments application_close_selected {owner child program run cgroup_fd ticks start read_offset group resume_offset} _.
Arguments application_options_at {owner child program run cgroup_fd ticks start read_offset group resume_offset} _.
Arguments application_close_at {owner child program run cgroup_fd ticks start read_offset group resume_offset} _.
Arguments application_options_tracer {owner child program run cgroup_fd ticks start read_offset group resume_offset} _.
Arguments application_close_group {owner child program run cgroup_fd ticks start read_offset group resume_offset} _.
Arguments application_options_before_close {owner child program run cgroup_fd ticks start read_offset group resume_offset} _.
Arguments application_close_before_resume {owner child program run cgroup_fd ticks start read_offset group resume_offset} _.
Arguments application_close_before_read {owner child program run cgroup_fd ticks start read_offset group resume_offset} _.

Theorem recorded_fork_application_positions operation(linux:LinuxProcessContract operation)groups scope first snapshot run
    (fork:ActualSourceFork run(task_pid(fork_child snapshot)))
    (input:ParentPreparedInput scope first(source_fork_parent _ _ fork))
    owner child program channel ticks start read_offset read_tick
    (recorded:RecordedForkAdmission operation groups scope first snapshot run fork input owner child program channel
      ticks start read_offset read_tick)
    runs cursor worlds process_before_fork born other final final_worlds after group:
  SourceProgramOwner runs owner program ->nth_error runs program=Some run ->
  SourceOtherContract other groups(physical_identity_task owner)(physical_identity_task child) ->
  SourceProcessSchedule operation groups child runs program other cursor worlds born ticks final final_worlds after ->
  cursor program=S(length(source_fork_common _ _ fork)) ->
  fork_parent snapshot=physical_identity_task owner ->fork_child snapshot=physical_identity_task child ->
  ForkProcessEffect(worlds program)process_before_fork snapshot born ->
  namespace_sigchld(worlds program)=default_signal_action ->
  process_sole_waiter process_before_fork(fork_parent snapshot)=true ->
  SourceFileView groups born(physical_identity_task owner)(worlds program) ->
  process_cgroup_files born(physical_identity_task owner)(prepared_cgroup_fd input)=Some group ->
  LeanCage_Entry_CallerPhysical_ParentLiveBefore(Nat_of_nat start)(tick_values ticks)
    (Nat_of_nat(start+S(recorded_resume_offset recorded))) ->
  (forall tick,In tick ticks ->
    (forall ordinal,LeanCage_Entry_CallerPhysical_Tick_source tick<>source_reference program ordinal) ->
    LeanCage_Entry_CallerPhysical_WriteOutsideCgroup(recorded_cgroup_objects groups)tick) ->
  inhabited(ApplicationPositions owner child program run(prepared_cgroup_fd input)ticks start read_offset group
    (recorded_resume_offset recorded)).
Proof.
  intros OWNER PROGRAM CONTRACT RUN CURSOR PARENT CHILD FORK DEFAULT SOLE FILES FILE LIVE OTHER_QUIET.
  destruct(recorded_grant_actual_admission_source operation groups scope first snapshot run fork input owner child program channel
    ticks start read_offset read_tick recorded)as[slice].
  pose proof(source_process_schedule_tables _ _ _ _ _ _ _ _ _ _ _ _ _ RUN)as TABLES.
  assert(ACTOR:forall actual,nth_error runs program=Some actual ->source_actor actual=owner).
  { intros actual PRESENT;eapply source_owner_actor;eassumption. }
  assert(TASK_ACTOR:forall actual,nth_error runs program=Some actual ->
    physical_identity_task(source_actor actual)=physical_identity_task owner).
  { intros actual PRESENT;rewrite(ACTOR _ PRESENT);reflexivity. }
  assert(INITIAL_OWNER:OwnsUnreaped born(physical_identity_task owner)(physical_identity_task child)).
  { rewrite <-PARENT,<-CHILD;eapply source_default_fork_produces_unreaped;eassumption. }
  assert(CLOSE_LOWER:(cursor program<=admission_close_ordinal slice)%nat).
  { rewrite CURSOR,(admission_close_ordinal_exact slice),(admission_source_prefix_exact slice).
    repeat rewrite length_app;rewrite repeat_length;cbn;lia. }
  destruct(source_table_before_selected _ _ _ _ _ _ _ (recorded_resume_offset recorded)(recorded_resume_tick recorded)
    program(recorded_source_resume recorded)(admission_close_ordinal slice)run
    (namespace_process(process_entry(entry_library(close_returned(prepared_cgroup_fd input)(admission_close_reply slice)))))
    TABLES(recorded_resume_selected recorded)(recorded_resume_reference recorded)
    ltac:(split;[exact CLOSE_LOWER|exact(admission_close_before_resume slice)])PROGRAM(admission_close_selected slice))
    as[close_offset[close_tick[close_snapshot[CLOSE_BEFORE[CLOSE_SELECTED[CLOSE_REFERENCE CLOSE_PRIMITIVE]]]]]].
  destruct(nth_error_split _ _ CLOSE_SELECTED)as[close_prefix[close_suffix[TICKS CLOSE_OFFSET]]].
  assert(TO_CLOSE:SourceProcessSchedule operation groups child runs program other cursor worlds born
    ((close_prefix++[close_tick])++close_suffix)final final_worlds after).
  { rewrite <-app_assoc;cbn;rewrite <-TICKS;exact RUN. }
  destruct(source_process_schedule_split _ _ _ _ _ _ _ _ _ _ _ _ _ _ TO_CLOSE)
    as[close_cursor[close_worlds[closed_world[CLOSE_RUN CLOSE_TAIL]]]].
  assert(CLOSE_END:close_cursor program=S(admission_close_ordinal slice)).
  { eapply application_schedule_last_cursor;[exact CLOSE_RUN|exact CLOSE_REFERENCE]. }
  assert(CLOSE_AUTH:SourceOtherAuthority groups program(close_prefix++[close_tick])).
  { eapply source_other_authority_from_recorded_live with(prefix:=[])(suffix:=close_suffix)
      (start:=start)(limit:=(start+S(recorded_resume_offset recorded))%nat).
    - cbn;rewrite <-app_assoc;cbn;rewrite <-TICKS;exact LIVE.
    - cbn;rewrite length_app;cbn;rewrite CLOSE_OFFSET;lia.
    - intros tick MEMBER OUTSIDE;apply OTHER_QUIET;[rewrite TICKS;apply in_or_app|exact OUTSIDE].
      apply in_app_or in MEMBER;destruct MEMBER as[BEFORE|[SAME|EMPTY]].
      + left;exact BEFORE.
      + subst tick;right;left;reflexivity.
      + contradiction. }
  set(admit_start:=length(admission_source_prefix slice)).
  set(admit_end:=(admit_start+length(admission_source_events slice))%nat).
  assert(ADMIT_BOUNDS:(cursor program<=admit_start<=close_cursor program)%nat).
  { rewrite CURSOR,CLOSE_END,(admission_close_end slice).
    unfold admit_start;rewrite(admission_source_prefix_exact slice);repeat rewrite length_app;rewrite repeat_length;cbn;lia. }
  destruct(source_process_schedule_cut operation groups child runs program other cursor worlds born
    (close_prefix++[close_tick])close_cursor close_worlds closed_world admit_start CLOSE_RUN ADMIT_BOUNDS)
    as[prelude_ticks[remaining[admit_cursor[admit_worlds[admit_world CUT_FACTS]]]]].
  destruct CUT_FACTS as[CLOSE_PARTS[PRELUDE[REST ADMIT_START]]].
  assert(ADMIT_END_BOUNDS:(admit_cursor program<=admit_end<=close_cursor program)%nat).
  { rewrite ADMIT_START,CLOSE_END,(admission_close_end slice);unfold admit_end,admit_start;lia. }
  destruct(source_process_schedule_cut operation groups child runs program other admit_cursor admit_worlds admit_world
    remaining close_cursor close_worlds closed_world admit_end REST ADMIT_END_BOUNDS)
    as[admit_ticks[closing_ticks[after_cursor[after_worlds[admitted_world CUT_FACTS]]]]].
  destruct CUT_FACTS as[REMAINING[ADMISSION[CLOSING ADMIT_END]]].
  (* The actual quiet prelude retains the same fork lease and file view. *)
  set(prelude:=recorded_finish_prefix recorded++recorded_setup_prefix recorded++repeat namespace_source_event 15).
  assert(PRELUDE_QUIET:Forall(fun event=>namespace_parent_prelude_event event=true)prelude).
  { unfold prelude;rewrite app_assoc;apply Forall_app;split;[exact(recorded_setup_quiet recorded)|].
    apply namespace_parent_prelude_repeat;reflexivity. }
  destruct(admission_parent_prelude_process _ PRELUDE_QUIET)as[prelude_process[PRELUDE_EVENTS PRELUDE_PROCESS_QUIET]].
  set(common:=source_fork_common _ _ fork++[namespace_forked(task_pid(fork_child snapshot))]).
  assert(PREFIX:admission_source_prefix slice=common++prelude).
  { unfold common,prelude;rewrite(admission_source_prefix_exact slice);repeat rewrite <-app_assoc;reflexivity. }
  assert(PRELUDE_SOURCE:source_events run=common++map namespace_process prelude_process++
    (map namespace_process(admission_source_events slice)++
      (repeat namespace_source_event(admission_close_guard slice)++admission_close_callback slice)++admission_source_suffix slice)).
  { rewrite(admission_source_full slice),PREFIX,<-PRELUDE_EVENTS;repeat rewrite <-app_assoc;reflexivity. }
  assert(PRELUDE_CURSOR:cursor program=length common).
  { unfold common;rewrite length_app;cbn;rewrite CURSOR;lia. }
  assert(PRELUDE_END:admit_cursor program=(length common+length prelude_process)%nat).
  { rewrite ADMIT_START;unfold admit_start;rewrite PREFIX,length_app,PRELUDE_EVENTS,length_map;reflexivity. }
  assert(PROCESS_PRELUDE:source_program_process_events runs program prelude_ticks=prelude_process).
  { eapply source_process_schedule_event_slice;eassumption. }
  assert(PRELUDE_AUTH:SourceOtherAuthority groups program prelude_ticks).
  { eapply application_source_authority_subset;[exact CLOSE_AUTH|].
    intros tick MEMBER;rewrite CLOSE_PARTS;apply in_or_app;left;exact MEMBER. }
  destruct(source_process_schedule_files operation linux groups child runs program other(physical_identity_task owner)
    cursor worlds born prelude_ticks admit_cursor admit_worlds admit_world CONTRACT TASK_ACTOR PRELUDE INITIAL_OWNER
    PRELUDE_AUTH ltac:(rewrite PROCESS_PRELUDE;apply application_prelude_quiet;exact PRELUDE_PROCESS_QUIET)FILES)
    as[ADMIT_OWNER ADMIT_FILES].
  destruct(proj1(FILES _ _)FILE)as[cgroup_binding[cgroup_object[CGROUP_SLOT[CGROUP_OBJECT CGROUP_GROUP]]]].
  assert(FAILURE_OTHER:recorded_closed_failure recorded<>prepared_cgroup_fd input).
  { intro SAME;pose proof(recorded_closed_failure_child recorded)as FAILURE.
    rewrite SAME in FAILURE;destruct(fork_process_matches _ _ _ _ FORK)as[MP[MT TABLE]].
    rewrite TABLE,CGROUP_SLOT in FAILURE;inversion FAILURE;subst;
      cbn[endpoint_binding descriptor_object]in CGROUP_OBJECT;discriminate. }
  assert(PRELUDE_NOT_CLOSED:Forall(fun event=>namespace_parent_closed_fd event<>Some(prepared_cgroup_fd input))prelude).
  { unfold prelude;rewrite app_assoc;apply Forall_app;split.
    - eapply namespace_prelude_closes_exclude;[exact(recorded_setup_closes recorded)|].
      pose proof(prepared_cgroup_sources input)as[S0[S1[S2 S3]]];cbn;intuition congruence.
    - apply Forall_forall;intros event MEMBER;apply repeat_spec in MEMBER;subst;discriminate. }
  assert(PRELUDE_NAMESPACE:source_program_events runs program prelude_ticks=prelude).
  { eapply application_source_exact_slice;[eapply source_process_schedule_tables;exact PRELUDE|exact PROGRAM| |exact PRELUDE_CURSOR|].
    - rewrite PRELUDE_SOURCE,<-PRELUDE_EVENTS;reflexivity.
    - rewrite PRELUDE_END,PRELUDE_EVENTS,length_map;reflexivity. }
  assert(ADMIT_SLOT:namespace_table(admit_worlds program)(prepared_cgroup_fd input)=Some cgroup_binding).
  { eapply namespace_prelude_slot_steps;[exact PRELUDE_QUIET|exact PRELUDE_NOT_CLOSED| |exact CGROUP_SLOT].
    rewrite <-PRELUDE_NAMESPACE;eapply source_table_schedule_projects;[apply source_primitive_namespace_law|
      eapply source_process_schedule_tables;exact PRELUDE]. }
  assert(ADMIT_FILE:process_cgroup_files admit_world(physical_identity_task owner)(prepared_cgroup_fd input)=Some group).
  { apply(proj2(ADMIT_FILES _ _));exists cgroup_binding,cgroup_object;repeat split;assumption. }
  assert(ADMISSION_AUTH:SourceOtherAuthority groups program admit_ticks).
  { eapply application_source_authority_subset;[exact CLOSE_AUTH|].
    intros tick MEMBER;rewrite CLOSE_PARTS,REMAINING;apply in_or_app;right;apply in_or_app;left;exact MEMBER. }
  assert(CLOSING_AUTH:SourceOtherAuthority groups program closing_ticks).
  { eapply application_source_authority_subset;[exact CLOSE_AUTH|].
    intros tick MEMBER;rewrite CLOSE_PARTS,REMAINING;apply in_or_app;right;apply in_or_app;right;exact MEMBER. }
  assert(ADMIT_EVENTS:source_events run=admission_source_prefix slice++map namespace_process(admission_source_events slice)++
    ((repeat namespace_source_event(admission_close_guard slice)++admission_close_callback slice)++admission_source_suffix slice))
    by(rewrite(admission_source_full slice);repeat rewrite <-app_assoc;reflexivity).
  destruct(source_process_admission_options_checkpoint operation linux groups owner child runs program other
    admit_cursor admit_worlds admit_world admit_ticks after_cursor after_worlds admitted_world run(admission_source_prefix slice)
    ((repeat namespace_source_event(admission_close_guard slice)++admission_close_callback slice)++admission_source_suffix slice)
    (scope_cell scope)(recorded_ready recorded)(admission_source_events slice)(admission_source_after slice)
    (prepared_cgroup_fd input)group(prepared_status_cell input)Ptrofs.zero
    CONTRACT ACTOR ADMISSION ADMISSION_AUTH PROGRAM ADMIT_EVENTS ADMIT_START ADMIT_END
    (prepared_status_tls input)(recorded_ready_tls recorded)ADMIT_OWNER ADMIT_FILE
    ltac:(rewrite <-CHILD;exact(admission_source_run slice)))as[options_offset[options_tick[options_ordinal OPTIONS]]].
  (* The closing interval still ends at the selected physical close operation. *)
  assert(CLOSING_END:exists closing_prefix,closing_ticks=closing_prefix++[close_tick]).
  { apply(application_last_suffix _ close_prefix(prelude_ticks++admit_ticks)closing_ticks close_tick).
    - rewrite CLOSE_PARTS,REMAINING;repeat rewrite app_assoc;reflexivity.
    - intro EMPTY;rewrite EMPTY in CLOSING.
      pose proof(application_empty_schedule_cursor _ _ _ _ _ _ _ _ _ _ _ _ CLOSING)as CURSORS.
      pose proof(f_equal(fun value=>value program)CURSORS)as SAME.
      cbv beta in SAME.
      rewrite ADMIT_END,CLOSE_END,(admission_close_end slice)in SAME.
      unfold admit_end,admit_start in SAME.
      rewrite(admission_close_callback_exact slice),length_app,repeat_length in SAME;cbn in SAME;lia. }
  destruct CLOSING_END as[closing_prefix CLOSING_END].
  assert(CLOSE_GROUP:Lean.eq
    (LeanCage_Entry_CallerPhysical_Context_cgroup(LeanCage_Entry_CallerPhysical_Tick_after close_tick))
    (ProcessImport.Option_some_inst1 Lean.Nat(Nat_of_nat group))).
  { assert(CLOSING_ACTUAL:SourceProcessSchedule operation groups child runs program other
      after_cursor after_worlds admitted_world(closing_prefix++[close_tick])close_cursor close_worlds closed_world)
      by(rewrite <-CLOSING_END;exact CLOSING).
    assert(CLOSING_ACTUAL_AUTH:SourceOtherAuthority groups program(closing_prefix++[close_tick]))
      by(rewrite <-CLOSING_END;exact CLOSING_AUTH).
    assert(FINISH:close_cursor program=(length(admission_source_prefix slice)+length(admission_source_events slice)+
      admission_close_guard slice+length(admission_close_callback slice))%nat)
      by(rewrite CLOSE_END,(admission_close_end slice);reflexivity).
    exact(actual_source_admission_close_checkpoint operation linux groups child runs program other(physical_identity_task owner)
      admit_cursor admit_worlds admit_world admit_ticks after_cursor after_worlds admitted_world
      closing_prefix close_tick close_cursor close_worlds closed_world run(admission_source_prefix slice)
      (admission_source_suffix slice)(admission_close_guard slice)(scope_cell scope)(recorded_ready recorded)
      (admission_source_events slice)(admission_source_after slice)(admission_close_callback slice)
      (admission_close_after slice)(prepared_cgroup_fd input)group(prepared_status_cell input)Ptrofs.zero
      (admission_close_ordinal slice)(admission_close_reply slice)
      CONTRACT TASK_ACTOR ADMISSION CLOSING_ACTUAL ADMISSION_AUTH CLOSING_ACTUAL_AUTH PROGRAM
      (admission_source_full slice)ADMIT_START ADMIT_END FINISH(prepared_status_tls input)(recorded_ready_tls recorded)
      ADMIT_OWNER ADMIT_FILE ltac:(rewrite <-CHILD;exact(admission_source_run slice))(admission_close_run slice)
      CLOSE_REFERENCE(admission_close_selected slice)). }
  set(global_options:=(length prelude_ticks+options_offset)%nat).
  assert(OPTIONS_BOUND:(options_offset<length admit_ticks)%nat).
  { apply nth_error_Some;rewrite(source_options_selected _ _ _ _ _ _ _ _ OPTIONS);discriminate. }
  assert(FULL_TICKS:ticks=prelude_ticks++admit_ticks++closing_ticks++close_suffix).
  { rewrite TICKS.
    replace(close_prefix++close_tick::close_suffix)with((close_prefix++[close_tick])++close_suffix)
      by(rewrite <-app_assoc;reflexivity).
    rewrite CLOSE_PARTS,REMAINING;repeat rewrite <-app_assoc;reflexivity. }
  assert(OPTIONS_SELECTED:nth_error ticks global_options=Some options_tick).
  { rewrite FULL_TICKS;unfold global_options;rewrite nth_error_app2 by lia.
    replace(length prelude_ticks+options_offset-length prelude_ticks)%nat with options_offset by lia.
    rewrite nth_error_app1 by exact OPTIONS_BOUND;exact(source_options_selected _ _ _ _ _ _ _ _ OPTIONS). }
  assert(OPTIONS_BEFORE:(global_options<=close_offset)%nat).
  { pose proof(source_options_selected _ _ _ _ _ _ _ _ OPTIONS)as AT.
    assert(BOUND:(options_offset<length admit_ticks)%nat)by(apply nth_error_Some;rewrite AT;discriminate).
    pose proof(f_equal(@length LeanCage_Entry_CallerPhysical_Tick)CLOSE_PARTS)as LENGTH.
    rewrite REMAINING,CLOSING_END,!length_app in LENGTH;cbn in LENGTH.
    rewrite CLOSE_OFFSET in LENGTH;unfold global_options;lia. }
  constructor;refine{|application_options_offset:=global_options;application_options_tick:=options_tick;
    application_close_offset:=close_offset;application_close_tick:=close_tick;
    application_close_ordinal:=admission_close_ordinal slice;application_close_reply:=admission_close_reply slice|};try assumption.
  - exact(admission_close_selected slice).
  - exact(admission_close_zero slice).
  - eapply actual_tick_position;exact OPTIONS_SELECTED.
  - eapply actual_tick_position;exact CLOSE_SELECTED.
  - exact(source_options_tracer _ _ _ _ _ _ _ _ OPTIONS).
  - destruct(recorded_physical_order recorded)as[RESUME_BEFORE SEND_BEFORE];lia.
Qed.
