(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.pid: One public source receipt joins the actual grant, scope checkpoint and retained authority. *)
From Stdlib Require Import List.
From compcert Require Import Integers Values Clight.
From LeanImport Require Import Lean.
From EntryProcess Require Import ProcessImport ProcessJournal ProcessOwnership ProcessPhysicalTrace
  ProcessSourceRecording ProcessSourceWorlds ProcessScope ProcessCgroupRecording.
From EntryNamespace Require Import NamespaceObjects NamespaceKernel NamespaceMemory NamespacePaths NamespaceChildResult NamespacePhysical
  NamespaceSourceFork NamespaceGrantInputs NamespaceAdmissionGuarantee NamespaceApplicationPositions
  NamespaceRecordedLiveness NamespaceCgroupAuthority.
Import ListNotations.
Local Close Scope lean_scope.

Record PublicSourceReceipt operation groups scope first snapshot run
    (fork:ActualSourceFork run(task_pid(fork_child snapshot)))
    (input:ParentPreparedInput scope first(source_fork_parent _ _ fork))
    owner child program channel ticks start read_offset read_tick
    (recorded:RecordedForkAdmission operation groups scope first snapshot run fork input owner child program channel
      ticks start read_offset read_tick)group:Type:={
  public_source_positions:ApplicationPositions owner child program run(prepared_cgroup_fd input)ticks start read_offset group
    (recorded_resume_offset recorded);
  public_source_resume_alive:Lean.eq(LeanCage_Entry_CallerPhysical_Context_parentAlive
    (LeanCage_Entry_CallerPhysical_Tick_before(recorded_resume_tick recorded)))ProcessImport.Bool_true;
  public_source_parent_absent:forall offset tick ordinal,nth_error ticks offset=Some tick ->
    (application_close_offset public_source_positions<offset)%nat ->
    LeanCage_Entry_CallerPhysical_Tick_source tick=source_reference program ordinal ->
    LeanCage_Entry_CallerPhysical_CgroupAbsent(recorded_cgroup_objects groups)tick owner;
  public_source_parent_writes:forall offset tick ordinal,nth_error ticks offset=Some tick ->
    (application_close_offset public_source_positions<offset)%nat ->
    LeanCage_Entry_CallerPhysical_Tick_source tick=source_reference program ordinal ->
    LeanCage_Entry_CallerPhysical_WriteOutsideCgroup(recorded_cgroup_objects groups)tick
}.

Arguments public_source_positions {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick recorded group} _.
Arguments public_source_resume_alive {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick recorded group} _.
Arguments public_source_parent_absent {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick recorded group} _.
Arguments public_source_parent_writes {operation groups scope first snapshot run fork input owner child program channel ticks start read_offset read_tick recorded group} _.

Theorem recorded_fork_public_source_receipt operation(linux:LinuxProcessContract operation)groups scope first snapshot run
    (fork:ActualSourceFork run(task_pid(fork_child snapshot)))
    (input:ParentPreparedInput scope first(source_fork_parent _ _ fork))
    owner child program channel ticks start read_offset read_tick
    (recorded:RecordedForkAdmission operation groups scope first snapshot run fork input owner child program channel
      ticks start read_offset read_tick)
    runs cursor worlds process_before_fork born other final final_worlds after group child_temps:
  SourceProgramOwner runs owner program ->nth_error runs program=Some run ->
  SourceOtherContract other groups(physical_identity_task owner)(physical_identity_task child) ->
  SourceProcessSchedule operation groups child runs program other cursor worlds born ticks final final_worlds after ->
  cursor program=S(length(source_fork_common _ _ fork)) ->
  source_cell run=scope_cell scope ->
  source_fork_continuation _ _ fork=child_fork_cont(storage_pair(scope_storage scope))child_temps(scope_continuation scope) ->
  fork_parent snapshot=physical_identity_task owner ->fork_child snapshot=physical_identity_task child ->
  ForkProcessEffect(worlds program)process_before_fork snapshot born ->
  namespace_sigchld(worlds program)=default_signal_action ->
  process_sole_waiter process_before_fork(fork_parent snapshot)=true ->
  SourceFileView groups born(physical_identity_task owner)(worlds program) ->
  process_cgroup_files born(physical_identity_task owner)(prepared_cgroup_fd input)=Some group ->
  PreparedCgroupHandles groups(namespace_table(worlds program))(prepared_cgroup_fd input) ->
  LeanCage_Entry_CallerPhysical_ParentLiveBefore(Nat_of_nat start)(tick_values ticks)
    (Nat_of_nat(start+S(recorded_resume_offset recorded))) ->
  (forall tick,In tick ticks ->
    (forall ordinal,LeanCage_Entry_CallerPhysical_Tick_source tick<>source_reference program ordinal) ->
    LeanCage_Entry_CallerPhysical_WriteOutsideCgroup(recorded_cgroup_objects groups)tick) ->
  (forall offset tick,nth_error ticks offset=Some tick ->SourceIO runs tick) ->
  inhabited(PublicSourceReceipt operation groups scope first snapshot run fork input owner child program channel
    ticks start read_offset read_tick recorded group).
Proof.
  intros OWNER PROGRAM CONTRACT RUN CURSOR CELL CONTINUATION PARENT CHILD FORK DEFAULT SOLE FILES FILE HANDLES LIVE OTHER_QUIET IO.
  destruct(recorded_fork_application_positions operation linux groups scope first snapshot run fork input owner child program
    channel ticks start read_offset read_tick recorded runs cursor worlds process_before_fork born other final final_worlds after group
    OWNER PROGRAM CONTRACT RUN CURSOR PARENT CHILD FORK DEFAULT SOLE FILES FILE LIVE OTHER_QUIET)as[positions].
  pose proof(source_process_schedule_tables _ _ _ _ _ _ _ _ _ _ _ _ _ RUN)as TABLES.
  constructor;refine{|public_source_positions:=positions|}.
  - eapply recorded_resume_parent_alive_strict;exact RUN.
  - intros offset tick ordinal SELECTED AFTER SOURCE.
    eapply actual_parent_closed_cgroup_absent;[exact TABLES|exact OWNER|exact PROGRAM|exact CURSOR|exact CELL|
      exact CONTINUATION|exact HANDLES|exact SELECTED|exact AFTER|exact SOURCE].
  - intros offset tick ordinal SELECTED AFTER SOURCE.
    eapply actual_parent_closed_cgroup_write_outside;[exact TABLES|exact OWNER|exact PROGRAM|exact CURSOR|exact CELL|
      exact CONTINUATION|exact HANDLES|exact SELECTED|exact AFTER|exact SOURCE|exact(IO offset tick SELECTED)].
Qed.
