(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.acceptance: The raw source/runtime journal is exactly the ordinary public journal. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers.
From LeanImport Require Import Lean.
From EntryProcess Require Import ProcessImport ProcessJournal ProcessOwnership ProcessPhysicalWitness
  ProcessLaunchRecordingWitness ProcessParentRecordingWitness ProcessPrimitiveWitness ProcessPrimitiveData
  ProcessPrimitiveRuns ProcessPrimitiveHistory.
Import ListNotations.
Local Close Scope lean_scope.
Local Open Scope nat_scope.

Lemma entry_tick_values_append first second:
  tick_values(first++second)=ProcessImport.List_append_inst1 LeanCage_Entry_CallerPhysical_Tick
    (tick_values first)(tick_values second).
Proof.
  induction first as[|tick ticks IH];[reflexivity|].
  change(ProcessImport.List_cons_inst1 LeanCage_Entry_CallerPhysical_Tick tick(tick_values(ticks++second))=
    ProcessImport.List_cons_inst1 LeanCage_Entry_CallerPhysical_Tick tick
      (ProcessImport.List_append_inst1 LeanCage_Entry_CallerPhysical_Tick(tick_values ticks)(tick_values second))).
  rewrite IH;reflexivity.
Qed.

Lemma entry_primitive_ticks_append family tables context first second:
  entry_primitive_ticks family tables context(first++second)=
    entry_primitive_ticks family tables context first++entry_primitive_ticks family tables context second.
Proof. unfold entry_primitive_ticks;apply map_app. Qed.

Lemma entry_context_traced_ordinary:
  primitive_context true task_running Int64.zero None=
    LeanCage_Entry_CallerWitness_tracedContext launch_recording_owner
      (LeanCage_Entry_CallerPhysical_born(Nat_of_nat 1)(ProcessImport.Option_none_inst1 Lean.Nat)).
Proof. reflexivity. Qed.

Theorem entry_worker_prefix_ordinary tables:
  tick_values(entry_worker_prefix tables)=
    LeanCage_Entry_CallerWitness_usefulWorkerPrefix launch_recording_owner launch_recording_child
      (entry_primitive_other_objects tables)(entry_primitive_other_flags tables).
Proof.
  unfold entry_worker_prefix;rewrite !app_assoc,!entry_tick_values_append,!entry_primitive_ticks_values.
  unfold LeanCage_Entry_CallerWitness_usefulWorkerPrefix.
  unfold entry_trace_tick,entry_stop_tick;rewrite primitive_context_born,entry_context_traced_ordinary.
  reflexivity.
Qed.

Theorem entry_worker_tail_ordinary tables:
  tick_values(entry_worker_tail tables)=ProcessImport.List_append_inst1 LeanCage_Entry_CallerPhysical_Tick
    (LeanCage_Entry_CallerWitness_usefulWorkerTail launch_recording_child
      (entry_primitive_other_objects tables)(entry_primitive_other_flags tables)
      (primitive_context true task_running(Int64.repr 1048592)(Some 1)))
    (ProcessImport.List_cons_inst1 LeanCage_Entry_CallerPhysical_Tick
      (LeanCage_Entry_CallerWitness_FDData_tick LeanCage_Entry_CallerPhysical_PrimitiveFamily_native
        launch_recording_child(entry_primitive_other_objects tables)(entry_primitive_other_flags tables)
        (primitive_context true task_running(Int64.repr 1048592)(Some 1))LeanCage_Entry_CallerPhysical_Action_native
        (primitive_context true task_running(Int64.repr 1048592)(Some 1))LeanCage_Entry_CallerWitness_FDData_execFrame)
      (ProcessImport.List_nil_inst1 LeanCage_Entry_CallerPhysical_Tick)).
Proof.
  unfold entry_worker_tail;rewrite entry_primitive_ticks_append,entry_tick_values_append,entry_primitive_ticks_values.
  reflexivity.
Qed.

Theorem entry_runtime_ticks_ordinary child_ticks parent_ticks prefix_tables tail_tables:
  tick_values(entry_runtime_ticks child_ticks parent_ticks prefix_tables tail_tables)=
    LeanCage_Entry_CallerWitness_usefulEntryTicks launch_recording_owner launch_recording_child
      (entry_primitive_other_objects prefix_tables)(entry_primitive_other_objects tail_tables)
      (entry_primitive_other_flags prefix_tables)(entry_primitive_other_flags tail_tables)
      (tick_values child_ticks)(tick_values parent_ticks)
      (primitive_context true task_running(Int64.repr 1048592)(Some 1)).
Proof.
  unfold entry_runtime_ticks,entry_worker_tail;rewrite entry_primitive_ticks_append.
  rewrite !app_assoc,!entry_tick_values_append,entry_worker_prefix_ordinary,entry_primitive_ticks_values.
  reflexivity.
Qed.
