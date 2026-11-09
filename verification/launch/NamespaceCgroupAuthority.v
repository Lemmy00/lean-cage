(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.pid: Actual post-close parent source has no cgroup-writing descriptor authority. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers Values Clight.
From LeanImport Require Import Lean.
Require Import Machine.
From EntryProcess Require Import ProcessImport ProcessJournal ProcessScope ProcessCgroupRecording
  ProcessSourceRecording ProcessSourceTables.
From EntryNamespace Require Import NamespaceObjects NamespaceKernel NamespaceWorldTrace NamespacePaths NamespaceCaller NamespaceMemory
  NamespaceChildResult NamespaceSourceFork NamespaceGrantInputs NamespaceDescriptorFrame NamespacePostForkClosure
  NamespacePhysicalGrant NamespaceSourceOwnership NamespaceApplicationPositions.
Import ListNotations.
Local Close Scope lean_scope.

(* Preparation exposes one owned cgroup descriptor. The property allows all
   ordinary descriptor aliases and every cgroup object absent from this table. *)
Definition PreparedCgroupHandles(groups:nat->option nat)table descriptor:=forall object group,
  groups object=Some group ->unique_object_alias table(ordinary_object object)descriptor.

Lemma cgroup_object_frame_unique before after object fd:
  descriptor_object_frame before after ->unique_object_alias before object fd ->unique_object_alias after object fd.
Proof.
  intros FRAME UNIQUE actual binding PRESENT OBJECT.
  destruct(FRAME _ _ PRESENT)as[previous[OLD SAME]];eapply UNIQUE;[exact OLD|congruence].
Qed.

Lemma cgroup_after_selected(A:Type)(prefix rest:list A)closed offset later:
  (length prefix<offset)%nat ->nth_error(prefix++closed::rest)offset=Some later ->
  nth_error rest(offset-S(length prefix))=Some later.
Proof.
  intros AFTER SELECTED;rewrite nth_error_app2 in SELECTED by lia.
  replace(offset-length prefix)%nat with(S(offset-S(length prefix)))in SELECTED by lia;exact SELECTED.
Qed.

Lemma source_program_write_actor runs owner program tick ordinal actor fd bytes lost:
  SourceProgramOwner runs owner program ->SourceIO runs tick ->
  LeanCage_Entry_CallerPhysical_Tick_source tick=source_reference program ordinal ->
  ProcessImport.socket tick=LeanCage_Entry_CallerPhysical_SocketObservation_wrote actor fd bytes lost ->actor=owner.
Proof.
  intros OWNER IO REFERENCE SOCKET;destruct(IO _ _ _ _ SOCKET)as[WRITE|OUTSIDE _];
    [|rewrite REFERENCE in OUTSIDE;discriminate].
  destruct WRITE as[actual selected index event io PROGRAM EVENT ACTUAL WRITING ACTOR FD BYTES LOST OBSERVED SOURCE].
  change(LeanCage_Entry_CallerPhysical_Tick_source tick=source_reference selected index)in SOURCE.
  assert(SAME:source_reference selected index=source_reference program ordinal)by congruence.
  destruct(source_reference_injective _ _ _ _ SAME)as[SELECTED ORDINAL];subst selected.
  rewrite ACTOR;eapply source_owner_actor;eassumption.
Qed.

Theorem actual_parent_closed_cgroup_absent operation groups child runs cursor worlds ticks final final_worlds
    scope first snapshot run(fork:ActualSourceFork run(task_pid(fork_child snapshot)))
    (input:ParentPreparedInput scope first(source_fork_parent _ _ fork))
    owner program start read_offset group resume_offset
    (positions:ApplicationPositions owner child program run(prepared_cgroup_fd input)ticks start read_offset group resume_offset)
    child_temps offset tick ordinal:
  SourceTableSchedule(SourcePrimitive operation groups child)runs cursor worlds ticks final final_worlds ->
  SourceProgramOwner runs owner program ->nth_error runs program=Some run ->
  cursor program=S(length(source_fork_common _ _ fork)) ->source_cell run=scope_cell scope ->
  source_fork_continuation _ _ fork=child_fork_cont(storage_pair(scope_storage scope))child_temps(scope_continuation scope) ->
  PreparedCgroupHandles groups(namespace_table(worlds program))(prepared_cgroup_fd input) ->
  nth_error ticks offset=Some tick ->(application_close_offset positions<offset)%nat ->
  LeanCage_Entry_CallerPhysical_Tick_source tick=source_reference program ordinal ->
  LeanCage_Entry_CallerPhysical_CgroupAbsent(recorded_cgroup_objects groups)tick owner.
Proof.
  intros TABLES OWNER PROGRAM CURSOR CELL CONTINUATION PREPARED SELECTED AFTER SOURCE.
  assert(ACTOR:source_actor run=owner)by(eapply source_owner_actor;eassumption).
  assert(PROFILE:Forall(fun event=>namespace_after_fork_event event=true)(skipn(cursor program)(source_events run))).
  { rewrite CURSOR,physical_grant_fork_body.
    pose proof(source_fork_suffix _ _ fork)as BODY;rewrite CELL,CONTINUATION,(prepared_parent_continuation input)in BODY.
    eapply actual_fork_return_no_capability_export;[exact(prepared_parent_global input)|exact BODY]. }
  destruct(nth_error_split _ _ (application_close_selected positions))as[prefix[rest[TICKS CLOSE_OFFSET]]].
  assert(LATER:nth_error rest(offset-S(length prefix))=Some tick).
  { eapply cgroup_after_selected;[rewrite CLOSE_OFFSET;exact AFTER|rewrite <-TICKS;exact SELECTED]. }
  assert(SCHEDULE:SourceTableSchedule(SourcePrimitive operation groups child)runs cursor worlds
    (prefix++application_close_tick positions::rest)final final_worlds)by(rewrite <-TICKS;exact TABLES).
  destruct(source_table_close_later_absence operation groups child runs cursor worlds prefix(application_close_tick positions)rest
    final final_worlds program(application_close_ordinal positions)run(prepared_cgroup_fd input)
    (application_close_reply positions)(offset-S(length prefix))tick ordinal SCHEDULE
    (application_close_reference positions)PROGRAM(application_close_source positions)(application_close_zero positions)LATER SOURCE)
    as[snapshot'[PRIMITIVE[BEFORE ABSENT]]].
  assert(PREFIX_EVENTS:Forall(fun event=>namespace_after_fork_event event=true)(source_program_events runs program prefix)).
  { destruct(source_table_schedule_split _ _ _ _ _ _ _ _ SCHEDULE)as[middle[middle_worlds[PREFIX SUFFIX]]].
    rewrite(source_table_schedule_program_events _ _ _ _ _ _ _ _ _ PREFIX PROGRAM).
    apply source_ownership_firstn;exact PROFILE. }
  assert(FRAME:descriptor_object_frame(namespace_table(worlds program))(namespace_table(source_namespace_before snapshot'))).
  { eapply namespace_after_fork_object_frame;[exact PREFIX_EVENTS|exact BEFORE]. }
  apply actual_cgroup_absence_produces_ordinary;intros object assigned GROUP.
  rewrite <-ACTOR;apply ABSENT;eapply cgroup_object_frame_unique;[exact FRAME|exact(PREPARED _ _ GROUP)].
Qed.

Theorem actual_parent_closed_cgroup_write_outside operation groups child runs cursor worlds ticks final final_worlds
    scope first snapshot run(fork:ActualSourceFork run(task_pid(fork_child snapshot)))
    (input:ParentPreparedInput scope first(source_fork_parent _ _ fork))
    owner program start read_offset group resume_offset
    (positions:ApplicationPositions owner child program run(prepared_cgroup_fd input)ticks start read_offset group resume_offset)
    child_temps offset tick ordinal:
  SourceTableSchedule(SourcePrimitive operation groups child)runs cursor worlds ticks final final_worlds ->
  SourceProgramOwner runs owner program ->nth_error runs program=Some run ->
  cursor program=S(length(source_fork_common _ _ fork)) ->source_cell run=scope_cell scope ->
  source_fork_continuation _ _ fork=child_fork_cont(storage_pair(scope_storage scope))child_temps(scope_continuation scope) ->
  PreparedCgroupHandles groups(namespace_table(worlds program))(prepared_cgroup_fd input) ->
  nth_error ticks offset=Some tick ->(application_close_offset positions<offset)%nat ->
  LeanCage_Entry_CallerPhysical_Tick_source tick=source_reference program ordinal ->
  SourceIO runs tick ->LeanCage_Entry_CallerPhysical_WriteOutsideCgroup(recorded_cgroup_objects groups)tick.
Proof.
  intros TABLES OWNER PROGRAM CURSOR CELL CONTINUATION PREPARED SELECTED AFTER SOURCE IO.
  pose proof(actual_parent_closed_cgroup_absent operation groups child runs cursor worlds ticks final final_worlds
    scope first snapshot run fork input owner program start read_offset group resume_offset positions child_temps offset tick ordinal
    TABLES OWNER PROGRAM CURSOR CELL CONTINUATION PREPARED SELECTED AFTER SOURCE)as ABSENT.
  intros actor fd bytes lost object BOUND WROTE PRESENT.
  assert(SOCKET:ProcessImport.socket tick=LeanCage_Entry_CallerPhysical_SocketObservation_wrote actor fd bytes lost)
    by(destruct WROTE;reflexivity).
  assert(ACTOR:actor=owner)by(eapply source_program_write_actor;eassumption).
  subst actor;exact(ABSENT fd object BOUND PRESENT).
Qed.
