(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.acceptance: Actual primitive data inhabit the shared process and kernel history. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Integers Values.
From LeanImport Require Import Lean.
Require Import Machine LibraryMachine.
From EntryProcess Require Import ProcessMachine ProcessImport ProcessJournal ProcessOwnership ProcessPhysicalWitness
  ProcessSourceRecording ProcessLaunchWitness ProcessLaunchRecordingWitness ProcessParentRecordingWitness
  ProcessWorkerOtherWitness ProcessRecordedComposition ProcessPrimitiveWitness ProcessPrimitiveData.
From EntryNamespace Require Import NamespaceObjects NamespacePhysical.
Import ListNotations.
Local Close Scope lean_scope.
Local Open Scope nat_scope.

Definition primitive_context traced phase options group:=
  source_recording_context launch_recording_owner traced phase options 1 group.
Definition primitive_frame_code(frame:EntryPrimitiveFrame):=
  nat_of_Nat(LeanCage_Entry_CallerWitness_FDData_Frame_code frame).
Definition primitive_native_frame(frame:EntryPrimitiveFrame):Prop:=
  primitive_frame_code frame<>2 /\primitive_frame_code frame<>3 /\primitive_frame_code frame<>24.
Definition primitive_metadata_frame(frame:EntryPrimitiveFrame):Prop:=
  primitive_frame_code frame=0 \/primitive_frame_code frame=1 \/primitive_frame_code frame=2.

Definition entry_primitive_ticks family tables context(frames:list EntryPrimitiveFrame):=
  map(entry_primitive_tick family tables context LeanCage_Entry_CallerPhysical_Action_native context)frames.

Theorem entry_primitive_ticks_values family tables context frames:
  tick_values(entry_primitive_ticks family tables context(primitive_frames frames))=
    LeanCage_Entry_CallerWitness_FDData_ticks family launch_recording_child
      (entry_primitive_other_objects tables)(entry_primitive_other_flags tables)context frames.
Proof.
  induction frames as[|frame frames IH];[reflexivity|].
  change(ProcessImport.List_cons_inst1 LeanCage_Entry_CallerPhysical_Tick
    (entry_primitive_tick family tables context LeanCage_Entry_CallerPhysical_Action_native context frame)
    (tick_values(entry_primitive_ticks family tables context(primitive_frames frames)))=
    ProcessImport.List_cons_inst1 LeanCage_Entry_CallerPhysical_Tick
    (entry_primitive_tick family tables context LeanCage_Entry_CallerPhysical_Action_native context frame)
    (LeanCage_Entry_CallerWitness_FDData_ticks family launch_recording_child
      (entry_primitive_other_objects tables)(entry_primitive_other_flags tables)context frames)).
  rewrite IH;reflexivity.
Qed.

Lemma primitive_process_view files(traced:bool)phase options group:
  SourceProcessView(launch_world files(if traced then Some physical_parent else None)phase options group)
    physical_child(primitive_context traced phase options group).
Proof.
  unfold primitive_context;apply source_recording_context_view;reflexivity.
Qed.

Lemma primitive_context_born:
  primitive_context false task_running Int64.zero None=
    LeanCage_Entry_CallerPhysical_born(Nat_of_nat 1)(ProcessImport.Option_none_inst1 Lean.Nat).
Proof. reflexivity. Qed.

Lemma primitive_context_stopped:
  primitive_context true task_traced_stop Int64.zero None=
    primitive_context true task_running Int64.zero None.
Proof. reflexivity. Qed.

Theorem entry_native_frame_process tables files(traced:bool)phase options group frame:
  primitive_native_frame frame ->
  UsefulWorkerOther(launch_world files(if traced then Some physical_parent else None)phase options group)
    (entry_primitive_tick LeanCage_Entry_CallerPhysical_PrimitiveFamily_native tables
      (primitive_context traced phase options group)LeanCage_Entry_CallerPhysical_Action_native
      (primitive_context traced phase options group)frame)
    (launch_world files(if traced then Some physical_parent else None)phase options group).
Proof.
  intros[TWO[THREE EXIT]].
  eapply useful_worker_native with(code:=primitive_frame_code frame).
  - apply entry_primitive_source.
  - unfold primitive_frame_code;rewrite Nat2natid;apply entry_primitive_label.
  - apply primitive_process_view.
  - apply primitive_process_view.
  - constructor;assumption.
Qed.

Theorem entry_metadata_frame_process tables files(traced:bool)phase options group frame:
  primitive_metadata_frame frame ->
  UsefulWorkerOther(launch_world files(if traced then Some physical_parent else None)phase options group)
    (entry_primitive_tick LeanCage_Entry_CallerPhysical_PrimitiveFamily_metadata tables
      (primitive_context traced phase options group)LeanCage_Entry_CallerPhysical_Action_native
      (primitive_context traced phase options group)frame)
    (launch_world files(if traced then Some physical_parent else None)phase options group).
Proof.
  intro CODE;eapply useful_worker_metadata with(code:=primitive_frame_code frame).
  - apply entry_primitive_source.
  - unfold primitive_frame_code;rewrite Nat2natid;apply entry_primitive_label.
  - exact CODE.
  - apply primitive_process_view.
  - apply primitive_process_view.
Qed.

Theorem entry_native_frames_process tables files(traced:bool)phase options group frames:
  Forall primitive_native_frame frames ->
  UsefulWorkerRun(launch_world files(if traced then Some physical_parent else None)phase options group)
    (entry_primitive_ticks LeanCage_Entry_CallerPhysical_PrimitiveFamily_native tables
      (primitive_context traced phase options group)frames)
    (launch_world files(if traced then Some physical_parent else None)phase options group).
Proof.
  intro FRAMES;induction FRAMES;cbn[entry_primitive_ticks map];[constructor|].
  econstructor;[apply entry_native_frame_process;exact H|exact IHFRAMES].
Qed.

Theorem entry_metadata_frames_process tables files(traced:bool)phase options group frames:
  Forall primitive_metadata_frame frames ->
  UsefulWorkerRun(launch_world files(if traced then Some physical_parent else None)phase options group)
    (entry_primitive_ticks LeanCage_Entry_CallerPhysical_PrimitiveFamily_metadata tables
      (primitive_context traced phase options group)frames)
    (launch_world files(if traced then Some physical_parent else None)phase options group).
Proof.
  intro FRAMES;induction FRAMES;cbn[entry_primitive_ticks map];[constructor|].
  econstructor;[apply entry_metadata_frame_process;exact H|exact IHFRAMES].
Qed.

Theorem entry_primitive_frames_recorded runs mayTrace family tables context frames:
  RecordedRun runs mayTrace launch_recording_owner launch_recording_child context
    (entry_primitive_ticks family tables context frames)context.
Proof.
  induction frames as[|frame frames IH];cbn[entry_primitive_ticks map];[constructor|].
  eapply recorded_next with(tick:=entry_primitive_tick family tables context
    LeanCage_Entry_CallerPhysical_Action_native context frame).
  - apply source_tick_native;reflexivity.
  - apply entry_primitive_frame_step.
  - exact IH.
Qed.

Definition entry_trace_tick tables:=
  entry_primitive_tick LeanCage_Entry_CallerPhysical_PrimitiveFamily_native tables
    (primitive_context false task_running Int64.zero None)LeanCage_Entry_CallerPhysical_Action_traceMe
    (primitive_context true task_running Int64.zero None)(primitive_pack 2 0 0).
Definition entry_stop_tick tables:=
  entry_primitive_tick LeanCage_Entry_CallerPhysical_PrimitiveFamily_native tables
    (primitive_context true task_running Int64.zero None)LeanCage_Entry_CallerPhysical_Action_native
    (primitive_context true task_running Int64.zero None)(primitive_pack 3 0 0).

Theorem entry_trace_process tables files:
  UsefulWorkerOther(launch_world files None task_running Int64.zero None)(entry_trace_tick tables)
    (launch_world files(Some physical_parent)task_running Int64.zero None).
Proof.
  eapply useful_worker_native with(code:=2).
  - apply entry_primitive_source.
  - apply entry_primitive_label.
  - exact(primitive_process_view files false task_running Int64.zero None).
  - exact(primitive_process_view files true task_running Int64.zero None).
  - constructor.
Qed.

Theorem entry_stop_process tables files:
  UsefulWorkerOther(launch_world files(Some physical_parent)task_running Int64.zero None)(entry_stop_tick tables)
    (launch_world files(Some physical_parent)task_traced_stop Int64.zero None).
Proof.
  eapply useful_worker_native with(code:=3).
  - apply entry_primitive_source.
  - apply entry_primitive_label.
  - exact(primitive_process_view files true task_running Int64.zero None).
  - change(SourceProcessView(launch_world files(Some physical_parent)task_traced_stop Int64.zero None)
      physical_child(primitive_context true task_running Int64.zero None)).
    rewrite <-primitive_context_stopped;exact(primitive_process_view files true task_traced_stop Int64.zero None).
  - constructor.
Qed.

Theorem entry_trace_recorded runs mayTrace tables:
  RecordedRun runs mayTrace launch_recording_owner launch_recording_child
    (primitive_context false task_running Int64.zero None)[entry_trace_tick tables]
    (primitive_context true task_running Int64.zero None).
Proof.
  eapply recorded_next with(tick:=entry_trace_tick tables).
  - apply source_tick_traceme;reflexivity.
  - apply LeanCage_Entry_CallerPhysical_Step_traceMe;constructor.
  - constructor.
Qed.

Theorem entry_stop_recorded runs mayTrace tables:
  RecordedRun runs mayTrace launch_recording_owner launch_recording_child
    (primitive_context true task_running Int64.zero None)[entry_stop_tick tables]
    (primitive_context true task_running Int64.zero None).
Proof.
  eapply recorded_next with(tick:=entry_stop_tick tables).
  - apply source_tick_native;reflexivity.
  - apply entry_primitive_frame_step.
  - constructor.
Qed.

Lemma primitive_inspection_codes:
  Forall primitive_metadata_frame(primitive_frames LeanCage_Entry_CallerWitness_FDData_inspectionFrames).
Proof. vm_compute;repeat constructor;congruence. Qed.
Lemma primitive_signal_codes:
  Forall primitive_native_frame(primitive_frames LeanCage_Entry_CallerWitness_FDData_signalFrames).
Proof. vm_compute;repeat constructor;congruence. Qed.
Lemma primitive_tail_codes:
  Forall primitive_native_frame(primitive_frames LeanCage_Entry_CallerWitness_FDData_tailFrames).
Proof. vm_compute;repeat constructor;congruence. Qed.
Lemma primitive_exec_code:primitive_native_frame(primitive_pack 23 6 7).
Proof. vm_compute;repeat split;discriminate. Qed.

Definition entry_worker_prefix tables:=
  entry_primitive_ticks LeanCage_Entry_CallerPhysical_PrimitiveFamily_metadata tables
    (primitive_context false task_running Int64.zero None)
    (primitive_frames LeanCage_Entry_CallerWitness_FDData_inspectionFrames)++
  entry_primitive_ticks LeanCage_Entry_CallerPhysical_PrimitiveFamily_metadata tables
    (primitive_context false task_running Int64.zero None)
    (primitive_frames LeanCage_Entry_CallerWitness_FDData_inspectionFrames)++
  entry_primitive_ticks LeanCage_Entry_CallerPhysical_PrimitiveFamily_native tables
    (primitive_context false task_running Int64.zero None)
    (primitive_frames LeanCage_Entry_CallerWitness_FDData_signalFrames)++[entry_trace_tick tables;entry_stop_tick tables].
Definition entry_worker_tail tables:=
  entry_primitive_ticks LeanCage_Entry_CallerPhysical_PrimitiveFamily_native tables
    (primitive_context true task_running(Int64.repr 1048592)(Some 1))
    (primitive_frames LeanCage_Entry_CallerWitness_FDData_tailFrames++[primitive_pack 23 6 7]).

Lemma entry_worker_prefix_length tables:length(entry_worker_prefix tables)=74.
Proof.
  unfold entry_worker_prefix,entry_primitive_ticks;repeat rewrite app_length;repeat rewrite map_length;reflexivity.
Qed.
Lemma entry_worker_tail_length tables:length(entry_worker_tail tables)=69.
Proof.
  unfold entry_worker_tail,entry_primitive_ticks;rewrite map_length,app_length;reflexivity.
Qed.

Theorem entry_worker_prefix_process tables:
  UsefulWorkerRun(launch_world launch_parent_files None task_running Int64.zero None)(entry_worker_prefix tables)
    (launch_world launch_parent_files(Some physical_parent)task_traced_stop Int64.zero None).
Proof.
  unfold entry_worker_prefix.
  eapply useful_worker_run_append;
    [exact(entry_metadata_frames_process tables launch_parent_files false task_running Int64.zero None _
      primitive_inspection_codes)|].
  eapply useful_worker_run_append;
    [exact(entry_metadata_frames_process tables launch_parent_files false task_running Int64.zero None _
      primitive_inspection_codes)|].
  eapply useful_worker_run_append;
    [exact(entry_native_frames_process tables launch_parent_files false task_running Int64.zero None _
      primitive_signal_codes)|].
  econstructor;[apply entry_trace_process|]. econstructor;[apply entry_stop_process|constructor].
Qed.

Theorem entry_worker_prefix_recorded runs mayTrace tables:
  RecordedRun runs mayTrace launch_recording_owner launch_recording_child
    (primitive_context false task_running Int64.zero None)(entry_worker_prefix tables)
    (primitive_context true task_running Int64.zero None).
Proof.
  unfold entry_worker_prefix.
  eapply recorded_run_append;[apply entry_primitive_frames_recorded|].
  eapply recorded_run_append;[apply entry_primitive_frames_recorded|].
  eapply recorded_run_append;[apply entry_primitive_frames_recorded|].
  change(RecordedRun runs mayTrace launch_recording_owner launch_recording_child
    (primitive_context false task_running Int64.zero None)([entry_trace_tick tables]++[entry_stop_tick tables])
    (primitive_context true task_running Int64.zero None)).
  eapply recorded_run_append;[apply entry_trace_recorded|apply entry_stop_recorded].
Qed.

Theorem entry_worker_tail_process tables:
  UsefulWorkerRun(launch_world launch_empty_files(Some physical_parent)task_running(Int64.repr 1048592)(Some 1))
    (entry_worker_tail tables)
    (launch_world launch_empty_files(Some physical_parent)task_running(Int64.repr 1048592)(Some 1)).
Proof.
  apply(entry_native_frames_process tables launch_empty_files true task_running(Int64.repr 1048592)(Some 1)).
  apply Forall_app;split;[exact primitive_tail_codes|].
  constructor;[exact primitive_exec_code|constructor].
Qed.

Theorem entry_worker_tail_recorded runs mayTrace tables:
  RecordedRun runs mayTrace launch_recording_owner launch_recording_child
    (primitive_context true task_running(Int64.repr 1048592)(Some 1))(entry_worker_tail tables)
    (primitive_context true task_running(Int64.repr 1048592)(Some 1)).
Proof. apply entry_primitive_frames_recorded. Qed.
