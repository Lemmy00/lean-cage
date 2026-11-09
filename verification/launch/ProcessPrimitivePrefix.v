(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.origin: Each actual pre-grant worker operation preserves private authority. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers Values.
From LeanImport Require Import Lean.
Require Import Machine LibraryMachine.
From EntryProcess Require Import ProcessImport ProcessOwnership ProcessPhysicalWitness ProcessLaunchWitness
  ProcessLaunchRecordingWitness ProcessParentRecordingWitness ProcessCapabilityRecording ProcessNativeCapabilities
  ProcessRecordedComposition ProcessPrimitiveWitness ProcessPrimitiveData ProcessPrimitiveRuns ProcessPrimitiveHistory.
From EntryNamespace Require Import NamespaceObjects NamespaceCapabilities.
Import ListNotations.
Local Close Scope lean_scope.
Local Open Scope nat_scope.

Local Definition prefix_inspection_frames:=primitive_frames LeanCage_Entry_CallerWitness_FDData_inspectionFrames.
Local Definition prefix_signal_frames:=primitive_frames LeanCage_Entry_CallerWitness_FDData_signalFrames.
Local Definition prefix_inspection_plan:=primitive_plan LeanCage_Entry_CallerPhysical_PrimitiveFamily_metadata prefix_inspection_frames.
Local Definition prefix_signal_plan:=primitive_plan LeanCage_Entry_CallerPhysical_PrimitiveFamily_native prefix_signal_frames.
Local Definition prefix_inspection_ticks tables:=
  entry_primitive_ticks LeanCage_Entry_CallerPhysical_PrimitiveFamily_metadata tables
    (primitive_context false task_running Int64.zero None)prefix_inspection_frames.
Local Definition prefix_signal_ticks tables:=
  entry_primitive_ticks LeanCage_Entry_CallerPhysical_PrimitiveFamily_native tables
    (primitive_context false task_running Int64.zero None)prefix_signal_frames.

Ltac prefix_ticks_match:=
  unfold entry_runtime_ticks,entry_worker_prefix,prefix_inspection_ticks,prefix_signal_ticks;
  repeat rewrite <-app_assoc;reflexivity.
Ltac prefix_plan_matches:=
  unfold entry_primitive_plan,primitive_prefix_plan,prefix_inspection_plan,prefix_signal_plan,
    prefix_inspection_frames,prefix_signal_frames;
  repeat rewrite <-app_assoc;reflexivity.
Ltac prefix_lengths_match:=
  unfold prefix_inspection_ticks,prefix_signal_ticks,prefix_inspection_plan,prefix_signal_plan,
    entry_primitive_ticks,primitive_plan;
  repeat rewrite length_app;repeat rewrite length_map;repeat rewrite repeat_length;cbn[length];lia.

Theorem entry_worker_prefix_capabilities child_ticks parent_ticks prefix_tables tail_tables can_acquire external runs:
  (forall actor,launch_nonnegative_table(prefix_tables actor)) ->
  CapabilityHistory launch_operation launch_group_objects runs
    (entry_runtime_native child_ticks parent_ticks prefix_tables tail_tables can_acquire)
    (entry_runtime_metadata child_ticks parent_ticks prefix_tables tail_tables can_acquire)
    external can_acquire launch_recording_owner launch_recording_child
    (entry_primitive_capabilities prefix_tables(primitive_snapshot_table 0))
    (entry_worker_prefix prefix_tables)
    (entry_primitive_capabilities prefix_tables(primitive_snapshot_table 0)).
Proof.
  intro VALID.
  change(CapabilityHistory launch_operation launch_group_objects runs
    (entry_runtime_native child_ticks parent_ticks prefix_tables tail_tables can_acquire)
    (entry_runtime_metadata child_ticks parent_ticks prefix_tables tail_tables can_acquire)
    external can_acquire launch_recording_owner launch_recording_child
    (entry_primitive_capabilities prefix_tables(primitive_snapshot_table 0))
    (prefix_inspection_ticks prefix_tables++prefix_inspection_ticks prefix_tables++prefix_signal_ticks prefix_tables++
      [entry_trace_tick prefix_tables;entry_stop_tick prefix_tables])
    (entry_primitive_capabilities prefix_tables(primitive_snapshot_table 0))).
  eapply capability_history_append.
  - unfold entry_runtime_metadata,prefix_inspection_ticks.
    eapply entry_metadata_plan_history with(prefix:=child_ticks)
      (suffix:=prefix_inspection_ticks prefix_tables++prefix_signal_ticks prefix_tables++
        [entry_trace_tick prefix_tables;entry_stop_tick prefix_tables]++parent_ticks++entry_worker_tail tail_tables)
      (plan_prefix:=repeat None(length child_ticks))
      (plan_suffix:=prefix_inspection_plan++prefix_signal_plan++
        primitive_plan LeanCage_Entry_CallerPhysical_PrimitiveFamily_native[primitive_pack 2 0 0;primitive_pack 3 0 0]++
        repeat None(length parent_ticks)++primitive_tail_plan).
    + exact primitive_inspection_table_chain.
    + exact VALID.
    + exact primitive_context_untraced_safe.
    + intros frame MEMBER;apply primitive_inspection_code;exact MEMBER.
    + intros frame MEMBER;apply primitive_inspection_effect;exact MEMBER.
    + prefix_ticks_match.
    + prefix_plan_matches.
    + prefix_lengths_match.
  - eapply capability_history_append.
    + unfold entry_runtime_metadata,prefix_inspection_ticks.
      eapply entry_metadata_plan_history with(prefix:=child_ticks++prefix_inspection_ticks prefix_tables)
        (suffix:=prefix_signal_ticks prefix_tables++[entry_trace_tick prefix_tables;entry_stop_tick prefix_tables]++
          parent_ticks++entry_worker_tail tail_tables)
        (plan_prefix:=repeat None(length child_ticks)++prefix_inspection_plan)
        (plan_suffix:=prefix_signal_plan++
          primitive_plan LeanCage_Entry_CallerPhysical_PrimitiveFamily_native[primitive_pack 2 0 0;primitive_pack 3 0 0]++
          repeat None(length parent_ticks)++primitive_tail_plan).
      * exact primitive_inspection_table_chain.
      * exact VALID.
      * exact primitive_context_untraced_safe.
      * intros frame MEMBER;apply primitive_inspection_code;exact MEMBER.
      * intros frame MEMBER;apply primitive_inspection_effect;exact MEMBER.
      * prefix_ticks_match.
      * prefix_plan_matches.
      * prefix_lengths_match.
    + eapply capability_history_append.
      * unfold entry_runtime_native,prefix_signal_ticks.
        eapply entry_native_plan_history with
          (prefix:=child_ticks++prefix_inspection_ticks prefix_tables++prefix_inspection_ticks prefix_tables)
          (suffix:=[entry_trace_tick prefix_tables;entry_stop_tick prefix_tables]++parent_ticks++entry_worker_tail tail_tables)
          (plan_prefix:=repeat None(length child_ticks)++prefix_inspection_plan++prefix_inspection_plan)
          (plan_suffix:=primitive_plan LeanCage_Entry_CallerPhysical_PrimitiveFamily_native
            [primitive_pack 2 0 0;primitive_pack 3 0 0]++repeat None(length parent_ticks)++primitive_tail_plan).
        -- exact primitive_signal_table_chain.
        -- exact VALID.
        -- exact primitive_context_untraced_safe.
        -- intros frame MEMBER;apply primitive_signal_code;exact MEMBER.
        -- intros frame MEMBER;apply primitive_signal_retained;exact MEMBER.
        -- prefix_ticks_match.
        -- prefix_plan_matches.
        -- prefix_lengths_match.
      * change(CapabilityHistory launch_operation launch_group_objects runs
          (entry_runtime_native child_ticks parent_ticks prefix_tables tail_tables can_acquire)
          (entry_runtime_metadata child_ticks parent_ticks prefix_tables tail_tables can_acquire)
          external can_acquire launch_recording_owner launch_recording_child
          (entry_primitive_capabilities prefix_tables(primitive_snapshot_table 0))
          ([entry_trace_tick prefix_tables]++[entry_stop_tick prefix_tables])
          (entry_primitive_capabilities prefix_tables(primitive_snapshot_table 0))).
        eapply capability_history_append.
        -- unfold entry_runtime_native,entry_trace_tick.
           eapply entry_native_singleton_plan_history with
             (tables:=prefix_tables)
             (before:=primitive_context false task_running Int64.zero None)
             (action:=LeanCage_Entry_CallerPhysical_Action_traceMe)
             (after:=primitive_context true task_running Int64.zero None)(frame:=primitive_pack 2 0 0)
             (prefix:=child_ticks++prefix_inspection_ticks prefix_tables++prefix_inspection_ticks prefix_tables++
               prefix_signal_ticks prefix_tables)
             (suffix:=[entry_stop_tick prefix_tables]++parent_ticks++entry_worker_tail tail_tables)
             (plan_prefix:=repeat None(length child_ticks)++prefix_inspection_plan++prefix_inspection_plan++prefix_signal_plan)
             (plan_suffix:=primitive_plan LeanCage_Entry_CallerPhysical_PrimitiveFamily_native[primitive_pack 3 0 0]++
               repeat None(length parent_ticks)++primitive_tail_plan).
           ++ exact VALID.
           ++ exact primitive_context_untraced_safe.
           ++ change(2<=27);lia.
           ++ constructor;apply primitive_retained_same.
           ++ prefix_ticks_match.
           ++ prefix_plan_matches.
           ++ prefix_lengths_match.
        -- unfold entry_runtime_native,entry_stop_tick.
           eapply entry_native_singleton_plan_history with
             (tables:=prefix_tables)
             (before:=primitive_context true task_running Int64.zero None)
             (action:=LeanCage_Entry_CallerPhysical_Action_native)
             (after:=primitive_context true task_running Int64.zero None)(frame:=primitive_pack 3 0 0)
             (prefix:=child_ticks++prefix_inspection_ticks prefix_tables++prefix_inspection_ticks prefix_tables++
               prefix_signal_ticks prefix_tables++[entry_trace_tick prefix_tables])
             (suffix:=parent_ticks++entry_worker_tail tail_tables)
             (plan_prefix:=repeat None(length child_ticks)++prefix_inspection_plan++prefix_inspection_plan++prefix_signal_plan++
               primitive_plan LeanCage_Entry_CallerPhysical_PrimitiveFamily_native[primitive_pack 2 0 0])
             (plan_suffix:=repeat None(length parent_ticks)++primitive_tail_plan).
           ++ exact VALID.
           ++ exact primitive_context_traced_safe.
           ++ change(3<=27);lia.
           ++ constructor;apply primitive_retained_same.
           ++ prefix_ticks_match.
           ++ prefix_plan_matches.
           ++ prefix_lengths_match.
Qed.
