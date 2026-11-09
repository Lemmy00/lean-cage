(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.receipt: Derive worker observations from its actual primitive tables. *)
From Stdlib Require Import List.
From LeanImport Require Import Lean.
From EntryProcess Require Import ProcessImport ProcessJournal ProcessScopeRecording ProcessLaunchWitness
  ProcessParentRecordingWitness ProcessChildTickWitness ProcessEntryObservations ProcessPrimitiveWitness ProcessPrimitiveRuns.
From EntryNamespace Require Import NamespaceObjects NamespacePhysical.
Import ListNotations.
Local Close Scope lean_scope.

Theorem entry_primitive_placement_recordings groups family tables context frames:
  Forall(PlacementRecording groups)(entry_primitive_ticks family tables context frames).
Proof.
  induction frames as[|frame frames IH];cbn[entry_primitive_ticks map];[constructor|].
  constructor;[apply entry_primitive_placement_recording;left;reflexivity|exact IH].
Qed.

Theorem entry_worker_prefix_placement_recordings groups tables:
  Forall(PlacementRecording groups)(entry_worker_prefix tables).
Proof.
  unfold entry_worker_prefix.
  apply Forall_app;split;[apply entry_primitive_placement_recordings|].
  apply Forall_app;split;[apply entry_primitive_placement_recordings|].
  apply Forall_app;split;[apply entry_primitive_placement_recordings|].
  constructor;[unfold entry_trace_tick;apply entry_primitive_placement_recording;right;reflexivity|].
  constructor;[unfold entry_stop_tick;apply entry_primitive_placement_recording;left;reflexivity|constructor].
Qed.

Theorem entry_worker_tail_placement_recordings groups tables:
  Forall(PlacementRecording groups)(entry_worker_tail tables).
Proof. apply entry_primitive_placement_recordings. Qed.

Theorem entry_primitive_foreign_cgroup_observations family tables context frames:
  (forall actor,launch_nonnegative_table(tables actor)) ->
  (forall actor,actor<>1%nat ->actor<>2%nat ->tables actor=entry_foreign_tables actor) ->
  Forall EntryForeignCgroupAbsent(entry_primitive_ticks family tables context frames).
Proof.
  intros VALID FOREIGN;induction frames as[|frame frames IH];cbn[entry_primitive_ticks map];[constructor|].
  constructor;[apply entry_primitive_foreign_cgroup;assumption|exact IH].
Qed.

Theorem entry_worker_prefix_foreign_cgroup_observations tables:
  (forall actor,launch_nonnegative_table(tables actor)) ->
  (forall actor,actor<>1%nat ->actor<>2%nat ->tables actor=entry_foreign_tables actor) ->
  Forall EntryForeignCgroupAbsent(entry_worker_prefix tables).
Proof.
  intros VALID FOREIGN;unfold entry_worker_prefix.
  apply Forall_app;split;[apply entry_primitive_foreign_cgroup_observations;assumption|].
  apply Forall_app;split;[apply entry_primitive_foreign_cgroup_observations;assumption|].
  apply Forall_app;split;[apply entry_primitive_foreign_cgroup_observations;assumption|].
  constructor;[unfold entry_trace_tick;apply entry_primitive_foreign_cgroup;assumption|].
  constructor;[unfold entry_stop_tick;apply entry_primitive_foreign_cgroup;assumption|constructor].
Qed.

Theorem entry_worker_tail_foreign_cgroup_observations tables:
  (forall actor,launch_nonnegative_table(tables actor)) ->
  (forall actor,actor<>1%nat ->actor<>2%nat ->tables actor=entry_foreign_tables actor) ->
  Forall EntryForeignCgroupAbsent(entry_worker_tail tables).
Proof. apply entry_primitive_foreign_cgroup_observations. Qed.

Theorem entry_complete_placement_recordings groups parent_program child_program namespace_id
    child_table parent_table parent_ordinal child_ordinal parent_namespace parent_world parent_events parent_ticks parent_final parent_after
    child_namespace child_world child_events child_ticks child_final child_after prefix_tables tail_tables:
  ParentRecording groups parent_program namespace_id child_table parent_ordinal parent_namespace parent_world
    parent_events parent_ticks parent_final parent_after ->
  ChildRecording groups child_program namespace_id parent_table child_ordinal child_namespace child_world
    child_events child_ticks child_final child_after ->
  Forall(PlacementRecording groups)
    (child_ticks++entry_worker_prefix prefix_tables++parent_ticks++entry_worker_tail tail_tables).
Proof.
  intros PARENT CHILD.
  apply Forall_app;split;[eapply entry_child_placement_recordings;exact CHILD|].
  apply Forall_app;split;[apply entry_worker_prefix_placement_recordings|].
  apply Forall_app;split;[eapply entry_parent_placement_recordings;exact PARENT|].
  apply entry_worker_tail_placement_recordings.
Qed.

Theorem entry_complete_foreign_cgroup_observations parent_program child_program namespace_id
    child_table parent_table parent_ordinal child_ordinal parent_namespace parent_world parent_events parent_ticks parent_final parent_after
    child_namespace child_world child_events child_ticks child_final child_after prefix_tables tail_tables:
  ParentRecording launch_group_objects parent_program namespace_id child_table parent_ordinal parent_namespace parent_world
    parent_events parent_ticks parent_final parent_after ->
  ChildRecording launch_group_objects child_program namespace_id parent_table child_ordinal child_namespace child_world
    child_events child_ticks child_final child_after ->
  (forall actor,launch_nonnegative_table(prefix_tables actor)) ->
  (forall actor,actor<>1%nat ->actor<>2%nat ->prefix_tables actor=entry_foreign_tables actor) ->
  (forall actor,launch_nonnegative_table(tail_tables actor)) ->
  (forall actor,actor<>1%nat ->actor<>2%nat ->tail_tables actor=entry_foreign_tables actor) ->
  Forall EntryForeignCgroupAbsent
    (child_ticks++entry_worker_prefix prefix_tables++parent_ticks++entry_worker_tail tail_tables).
Proof.
  intros PARENT CHILD PREFIX_VALID PREFIX_FOREIGN TAIL_VALID TAIL_FOREIGN.
  apply Forall_app;split;[eapply entry_child_foreign_cgroup_observations;exact CHILD|].
  apply Forall_app;split;[apply entry_worker_prefix_foreign_cgroup_observations;assumption|].
  apply Forall_app;split;[eapply entry_parent_foreign_cgroup_observations;exact PARENT|].
  apply entry_worker_tail_foreign_cgroup_observations;assumption.
Qed.
