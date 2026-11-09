(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.receipt: Derive shared source positions from the actual public receipt. *)
From Stdlib Require Import List Lia.
From compcert Require Import Integers Values.
From LeanImport Require Import Lean.
From EntryProcess Require Import ProcessImport ProcessJournal ProcessJournalLiveness ProcessSourceWorlds ProcessOwnership
  ProcessPhysicalTrace ProcessSourceRecording ProcessCgroupRecording.
From EntryNamespace Require Import NamespaceObjects NamespaceSourceFork NamespaceGrantInputs NamespaceAdmissionGuarantee
  NamespaceKernel NamespacePhysical NamespacePaths NamespaceMemory NamespaceChildResult
  NamespaceApplicationPositions NamespacePublicReceipt NamespaceRecordedLiveness NamespaceCgroupAuthority.
Import ListNotations.
Local Close Scope lean_scope.

Lemma scope_strict_less before after:
  (before<after)%nat ->(Nat_of_nat before<Nat_of_nat after)%Nat.
Proof.
  intro LESS;change((Nat_of_nat(S before)<=Nat_of_nat after)%Nat).
  apply nat_le_Nat_le;rewrite !nat2Natid;exact LESS.
Qed.

Definition public_scope_inputs operation groups scope first snapshot run
    (fork:ActualSourceFork run(task_pid(fork_child snapshot)))
    (input:ParentPreparedInput scope first(source_fork_parent _ _ fork))
    owner child program channel ticks start read_offset read_tick
    (recorded:RecordedForkAdmission operation groups scope first snapshot run fork input owner child program channel
      ticks start read_offset read_tick)group
    (public:PublicSourceReceipt operation groups scope first snapshot run fork input owner child program channel ticks
      start read_offset read_tick recorded group):
  LeanCage_Entry_SourceScopeInputs owner child(tick_values ticks)(Nat_of_nat read_offset)read_tick(Nat_of_nat group).
Proof.
  pose(positions:=public_source_positions public).
  refine(LeanCage_Entry_SourceScopeInputs_mk owner child(tick_values ticks)(Nat_of_nat read_offset)read_tick(Nat_of_nat group)
    (Nat_of_nat program)(Nat_of_nat(application_close_ordinal positions))(Nat_of_nat(application_close_offset positions))
    (application_close_tick positions)(application_close_at positions)_ (application_close_group positions)
    (Nat_of_nat(application_options_offset positions))(application_options_tick positions)(application_options_at positions)
    (application_options_tracer positions)_ (Nat_of_nat(recorded_source_resume recorded))(Nat_of_nat(recorded_resume_offset recorded))
    (recorded_resume_tick recorded)(recorded_resume_at recorded)_ _ _
    (Nat_of_nat(recorded_source_ordinal recorded))(Nat_of_nat(recorded_send_offset recorded))(recorded_send_tick recorded)
    (recorded_send_at recorded)_ _ _(recorded_read_at recorded)).
  - rewrite(application_close_reference positions);constructor.
  - apply nat_le_Nat_le;rewrite !nat2Natid;exact(application_options_before_close positions).
  - rewrite(recorded_resume_reference recorded);constructor.
  - rewrite(recorded_resume_action recorded);constructor.
  - apply scope_strict_less;exact(application_close_before_resume positions).
  - rewrite(recorded_source_reference recorded);constructor.
  - apply scope_strict_less;exact(proj1(recorded_physical_order recorded)).
  - apply scope_strict_less;exact(proj2(recorded_physical_order recorded)).
Defined.

Theorem recorded_source_parent_live operation groups scope first snapshot run
    (fork:ActualSourceFork run(task_pid(fork_child snapshot)))
    (input:ParentPreparedInput scope first(source_fork_parent _ _ fork))
    owner child program channel ticks start read_offset read_tick
    (recorded:RecordedForkAdmission operation groups scope first snapshot run fork input owner child program channel
      ticks start read_offset read_tick)
    runs cursor worlds born other final final_worlds after mayTrace history namespace cgroup context:
  SourceProcessSchedule operation groups child runs program other cursor worlds born ticks final final_worlds after ->
  LeanCage_Entry_CallerPhysical_Journal mayTrace owner child history
    (LeanCage_Entry_CallerPhysical_born namespace cgroup)(tick_values ticks)context ->
  LeanCage_Entry_CallerPhysical_ParentLiveBefore(Nat_of_nat start)(tick_values ticks)
    (Nat_of_nat(start+S(recorded_resume_offset recorded))).
Proof.
  intros SOURCE JOURNAL.
  pose proof(recorded_resume_parent_alive_strict operation groups scope first snapshot run fork input owner child program channel
    ticks start read_offset read_tick recorded runs cursor worlds born other final final_worlds after SOURCE)as BEFORE.
  pose proof(journal_selected_request_live _ _ _ _ _ _ _ _ _ _ _ _ JOURNAL(recorded_resume_selected recorded)
    (recorded_resume_action recorded)BEFORE)as LIVE.
  replace(start+S(recorded_resume_offset recorded))%nat with(start+recorded_resume_offset recorded+1)%nat by lia.
  eapply journal_parent_live_before_checkpoint;[exact JOURNAL|exact(recorded_resume_selected recorded)|exact LIVE].
Qed.

Theorem recorded_fork_public_source_from_journal operation(linux:LinuxProcessContract operation)groups scope first snapshot run
    (fork:ActualSourceFork run(task_pid(fork_child snapshot)))
    (input:ParentPreparedInput scope first(source_fork_parent _ _ fork))
    owner child program channel ticks start read_offset read_tick
    (recorded:RecordedForkAdmission operation groups scope first snapshot run fork input owner child program channel
      ticks start read_offset read_tick)
    runs cursor worlds process_before_fork born other final final_worlds after group child_temps mayTrace history namespace cgroup context:
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
  LeanCage_Entry_CallerPhysical_Journal mayTrace owner child history
    (LeanCage_Entry_CallerPhysical_born namespace cgroup)(tick_values ticks)context ->
  (forall tick,In tick ticks ->
    (forall ordinal,LeanCage_Entry_CallerPhysical_Tick_source tick<>source_reference program ordinal) ->
    LeanCage_Entry_CallerPhysical_WriteOutsideCgroup(recorded_cgroup_objects groups)tick) ->
  (forall offset tick,nth_error ticks offset=Some tick ->SourceIO runs tick) ->
  inhabited(PublicSourceReceipt operation groups scope first snapshot run fork input owner child program channel
    ticks start read_offset read_tick recorded group).
Proof.
  intros OWNER PROGRAM CONTRACT RUN CURSOR CELL CONTINUATION PARENT CHILD FORK DEFAULT SOLE FILES FILE HANDLES JOURNAL OTHER_QUIET IO.
  pose proof(recorded_source_parent_live operation groups scope first snapshot run fork input owner child program channel
    ticks start read_offset read_tick recorded runs cursor worlds born other final final_worlds after
    mayTrace history namespace cgroup context RUN JOURNAL)as LIVE.
  eapply(recorded_fork_public_source_receipt operation linux groups scope first snapshot run fork input owner child program channel
    ticks start read_offset read_tick recorded runs cursor worlds process_before_fork born other final final_worlds after group child_temps);
    eassumption.
Qed.
