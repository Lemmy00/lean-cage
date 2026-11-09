(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.acceptance: The same complete useful launch history transports its actual grant. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers Values.
From LeanImport Require Import Lean.
Require Import IO Machine LibraryMachine.
From EntryProcess Require Import ProcessMachine ProcessImport ProcessJournal ProcessOwnership ProcessPhysicalWitness ProcessNativeCapabilities
  ProcessSourceRecording ProcessLaunchWitness ProcessLaunchRecordingWitness ProcessParentRecordingWitness
  ProcessChildRecordingWitness ProcessChildTickWitness ProcessQueueWitness ProcessPrimitiveWitness ProcessPrimitiveData ProcessPrimitiveRuns
  ProcessEntryWitness.
From EntryNamespace Require Import NamespaceObjects NamespaceMachine NamespaceKernel NamespaceHandles NamespacePhysical NamespaceChannel NamespaceSocket
  NamespaceForkWorldWitness NamespaceSourceFork NamespaceLaunchWitness.
Import ListNotations.
Local Close Scope lean_scope.
Local Open Scope nat_scope.
Local Opaque launch_recording_owner launch_recording_child.

Definition entry_frame_quiet(frame:EntryPrimitiveFrame):Prop:=
  LeanCage_Entry_CallerWitness_FDData_Frame_read frame=
    ProcessImport.Option_none_inst1(ProcessImport.Prod_inst3 Lean.Nat(ProcessImport.List_inst1 Lean.Nat)).

Lemma entry_pack_quiet code before after:entry_frame_quiet(primitive_pack code before after).
Proof. reflexivity. Qed.

Lemma entry_quiet_tick family tables before action after frame:
  entry_frame_quiet frame ->
  ProcessImport.socket(entry_primitive_tick family tables before action after frame)=
    LeanCage_Entry_CallerPhysical_SocketObservation_none.
Proof.
  intro QUIET.
  change(LeanCage_Entry_CallerWitness_FDData_socket launch_recording_child
    (LeanCage_Entry_CallerWitness_FDData_Frame_read frame)=
      LeanCage_Entry_CallerPhysical_SocketObservation_none).
  rewrite QUIET;reflexivity.
Qed.

Lemma entry_quiet_frames_queue channel buffers family tables context frames:
  Forall entry_frame_quiet frames ->
  physical_queue_execution channel buffers(entry_primitive_ticks family tables context frames)buffers.
Proof.
  intro QUIET;induction QUIET;cbn[entry_primitive_ticks map];[constructor|].
  econstructor;[apply queue_socket_none,entry_quiet_tick;exact H|exact IHQUIET].
Qed.

Lemma entry_signal_quiet:
  Forall entry_frame_quiet(primitive_frames LeanCage_Entry_CallerWitness_FDData_signalFrames).
Proof.
  rewrite primitive_signal_values;constructor;[apply entry_pack_quiet|].
  apply Forall_app;split.
  - apply Forall_forall;intros frame MEMBER;apply repeat_spec in MEMBER;subst frame;apply entry_pack_quiet.
  -
  constructor;[apply entry_pack_quiet|constructor].
Qed.
Lemma entry_inspection_quiet:
  Forall entry_frame_quiet(primitive_frames LeanCage_Entry_CallerWitness_FDData_inspectionFrames).
Proof.
  change(Forall entry_frame_quiet
    [primitive_pack 0 0 1;primitive_pack 1 1 1;primitive_pack 1 1 1;primitive_pack 2 1 0]).
  repeat constructor.
Qed.

Theorem entry_worker_prefix_queue tables channel buffers:
  physical_queue_execution channel buffers(entry_worker_prefix tables)buffers.
Proof.
  unfold entry_worker_prefix.
  eapply queue_execution_append;[apply entry_quiet_frames_queue;exact entry_inspection_quiet|].
  eapply queue_execution_append;[apply entry_quiet_frames_queue;exact entry_inspection_quiet|].
  eapply queue_execution_append;[apply entry_quiet_frames_queue;exact entry_signal_quiet|].
  apply queue_sockets_none;repeat constructor.
Qed.

Definition entry_tail_context:=primitive_context true task_running(Int64.repr 1048592)(Some 1).
Definition entry_read_tick tables:=entry_primitive_tick LeanCage_Entry_CallerPhysical_PrimitiveFamily_native tables
  entry_tail_context LeanCage_Entry_CallerPhysical_Action_native entry_tail_context primitive_read_frame.
Definition entry_tail_remaining_frames:=
  [primitive_pack 4 0 2;primitive_pack 4 2 3;primitive_pack 4 3 4;primitive_pack 5 4 5;primitive_pack 6 5 6]++
  map(fun code=>primitive_pack code 6 6)ProcessPrimitiveData.primitive_tail_codes++[primitive_pack 23 6 7].

Lemma entry_tail_remaining_quiet:Forall entry_frame_quiet entry_tail_remaining_frames.
Proof.
  unfold entry_tail_remaining_frames;repeat(apply Forall_app;split).
  - repeat constructor.
  - apply Forall_map,Forall_forall;intros code MEMBER;apply entry_pack_quiet.
  - repeat constructor.
Qed.

Lemma entry_tail_read_cut tables:
  entry_worker_tail tables=entry_read_tick tables::
    entry_primitive_ticks LeanCage_Entry_CallerPhysical_PrimitiveFamily_native tables
      entry_tail_context entry_tail_remaining_frames.
Proof.
  unfold entry_worker_tail;rewrite primitive_tail_exact.
  unfold primitive_tail_values,entry_tail_remaining_frames,entry_primitive_ticks;rewrite !map_app;reflexivity.
Qed.

Lemma entry_read_socket tables:
  ProcessImport.socket(entry_read_tick tables)=
    LeanCage_Entry_CallerPhysical_SocketObservation_read launch_recording_child
      (native_descriptor_number(Int.repr 60))(Nat_of_nat 1)physical_grant_bytes.
Proof. reflexivity. Qed.

Lemma entry_read_binding tables:
  physical_tick_table(entry_read_tick tables)
    (nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey launch_recording_child))(Int.repr 60)=
      Some{|descriptor_object:=release_endpoint 60 child_endpoint;descriptor_cloexec:=false|}.
Proof.
  unfold physical_tick_table;rewrite Nat2natid.
  unfold entry_read_tick;rewrite entry_primitive_child_objects,entry_primitive_child_flags.
  change(capability_descriptor_table
    (LeanCage_Entry_CallerWitness_FDData_objects(primitive_snapshot 0))
    (LeanCage_Entry_CallerWitness_FDData_flags(primitive_snapshot 0))(Int.repr 60)=
      Some{|descriptor_object:=release_endpoint 60 child_endpoint;descriptor_cloexec:=false|}).
  rewrite primitive_initial_table;reflexivity.
Qed.

Theorem entry_worker_tail_queue tables:
  physical_queue_execution 60(channel_enqueue channel_empty 1 parent_endpoint[Byte.repr 165])
    (entry_worker_tail tables)channel_empty.
Proof.
  rewrite entry_tail_read_cut;econstructor.
  - eapply queue_read_grant;[apply entry_read_socket|apply entry_read_binding|reflexivity].
  - apply entry_quiet_frames_queue;exact entry_tail_remaining_quiet.
Qed.

Theorem entry_same_source_recording_queue groups parent_program child_program namespace_id parent_table
    parent_ordinal child_ordinal child_namespace child_world child_events child_ticks child_final child_after
    parent_world parent_events parent_ticks parent_final parent_after
    cell e pair parameters memory suffix final request
    (shape:NamespaceUsefulParentShape cell e pair parameters memory suffix final request)
    prefix_tables tail_tables:
  ChildRecording groups child_program namespace_id parent_table child_ordinal child_namespace child_world
    child_events child_ticks child_final child_after ->
  Forall(fun event=>namespace_socket_io(namespace_process event)=None)child_events ->
  suffix=map namespace_process parent_events ->
  ParentRecording groups parent_program namespace_id fork_fixture_worker_table parent_ordinal fork_fixture_world
    parent_world parent_events parent_ticks parent_final parent_after ->
  physical_queue_execution 60 channel_empty
    (child_ticks++entry_worker_prefix prefix_tables++parent_ticks++entry_worker_tail tail_tables)channel_empty.
Proof.
  intros CHILD QUIET EVENTS PARENT.
  eapply queue_execution_append;[eapply queue_child_recording_frames;[exact CHILD|exact QUIET]|].
  eapply queue_execution_append;[apply entry_worker_prefix_queue|].
  eapply queue_execution_append;[eapply actual_parent_recording_grant_queue;[exact shape|exact EVENTS|exact PARENT]|].
  apply entry_worker_tail_queue.
Qed.

Theorem actual_prepared_recorded_entry_queue namespace_id(parent child:CallerSourceRun)
    (fork:ActualSourceFork parent(Int.repr 2))pair parent_events child_events parent_ticks child_ticks
    parent_namespace child_namespace prefix_tables tail_tables:
  UsefulPreparedSource parent fork pair ->
  source_fork_body _ _ fork=map namespace_process parent_events ->
  source_events child=map namespace_process child_events ->
  Forall(fun event=>namespace_socket_io event=None)(source_events child) ->
  ParentRecording launch_group_objects 0 namespace_id fork_fixture_worker_table 61 fork_fixture_world
    (launch_world launch_parent_files(Some physical_parent)task_traced_stop Int64.zero None)
    parent_events parent_ticks parent_namespace
    (launch_world launch_empty_files(Some physical_parent)task_running(Int64.repr 1048592)(Some 1)) ->
  ChildRecording launch_group_objects 1 namespace_id(namespace_table fork_fixture_world)0 child_fork_namespace
    (launch_world launch_fork_files None task_running Int64.zero None)child_events child_ticks child_namespace
    (launch_world launch_parent_files None task_running Int64.zero None) ->
  physical_queue_execution 60 channel_empty
    (child_ticks++entry_worker_prefix prefix_tables++parent_ticks++entry_worker_tail tail_tables)channel_empty.
Proof.
  intros PREPARED PARENT_EVENTS CHILD_EVENTS QUIET PARENT CHILD.
  destruct PREPARED as(initial &cell &command &source &prepared &e &memory &parameters &final &request
    &INITIAL &CELL &BEFORE &ENV &INPUT &PREPARATION &CONT &SAME &AFTER &[shape]).
  eapply entry_same_source_recording_queue;[exact shape|exact CHILD| |exact PARENT_EVENTS|exact PARENT].
  rewrite CHILD_EVENTS in QUIET;apply Forall_forall;intros event MEMBER.
  rewrite Forall_forall in QUIET;apply QUIET,in_map;exact MEMBER.
Qed.
