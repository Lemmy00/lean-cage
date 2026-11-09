(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.origin: Join primitive descriptor maps to the same source worlds. *)
From Stdlib Require Import ZArith List Lia FunctionalExtensionality.
From compcert Require Import Integers Values.
From LeanImport Require Import Lean.
From EntryProcess Require Import ProcessMachine ProcessImport ProcessOwnership ProcessPhysicalWitness
  ProcessSourceRecording ProcessLaunchWitness ProcessLaunchRecordingWitness ProcessParentRecordingWitness
  ProcessParentCapabilityWitness ProcessChildTickWitness ProcessPrimitiveWitness ProcessPrimitiveData
  ProcessPrimitiveRuns ProcessPrimitiveHistory.
From EntryNamespace Require Import NamespaceObjects NamespaceMachine NamespaceKernel NamespaceCapabilities NamespacePhysical NamespaceForkWorldWitness.
Import ListNotations.
Local Close Scope lean_scope.

Lemma primitive_initial_snapshot:primitive_snapshot_table 0=fork_fixture_worker_table.
Proof. exact primitive_initial_table. Qed.

Lemma entry_primitive_tables_identity tables:
  entry_primitive_capabilities tables(tables 2%nat)={|capability_tables:=tables;capability_messages:=[]|}.
Proof.
  unfold entry_primitive_capabilities;f_equal;apply functional_extensionality;intro actor.
  unfold task_table_put;destruct(Nat.eq_dec actor 2)as[SAME|OTHER].
  - subst actor;rewrite Nat.eqb_refl;reflexivity.
  - assert(NE:Nat.eqb actor 2=false)by(apply Nat.eqb_neq;exact OTHER);rewrite NE;reflexivity.
Qed.

Theorem entry_primitive_child_world parent namespace:
  namespace_table namespace=fork_fixture_worker_table ->
  entry_primitive_capabilities(launch_child_tables namespace parent)(primitive_snapshot_table 0)=
    child_recording_capabilities parent namespace.
Proof.
  intro TABLE;rewrite primitive_initial_snapshot,<-TABLE.
  change(entry_primitive_capabilities(launch_child_tables namespace parent)
    (launch_child_tables namespace parent 2%nat)=child_recording_capabilities parent namespace).
  rewrite entry_primitive_tables_identity;reflexivity.
Qed.

Theorem entry_primitive_parent_world namespace:
  entry_primitive_capabilities(launch_parent_tables namespace fork_fixture_worker_table)(primitive_snapshot_table 0)=
    parent_recording_capabilities fork_fixture_worker_table namespace.
Proof.
  rewrite primitive_initial_snapshot.
  change(entry_primitive_capabilities(launch_parent_tables namespace fork_fixture_worker_table)
    (launch_parent_tables namespace fork_fixture_worker_table 2%nat)=
    parent_recording_capabilities fork_fixture_worker_table namespace).
  rewrite entry_primitive_tables_identity;reflexivity.
Qed.

Theorem entry_parent_recording_final_nonnegative groups program namespace_id child ordinal namespace world events ticks
    after_namespace after_world:
  ParentRecording groups program namespace_id child ordinal namespace world events ticks after_namespace after_world ->
  launch_nonnegative_table(namespace_table namespace) ->launch_nonnegative_table(namespace_table after_namespace).
Proof.
  intro RUN;induction RUN;intro VALID;[exact VALID|apply IHRUN].
  eapply launch_namespace_nonnegative;[exact(source_primitive_namespace _ _ _ _ _ _ _ H)|exact VALID].
Qed.

Theorem entry_primitive_child_tables_nonnegative namespace:
  namespace_table namespace=fork_fixture_worker_table ->
  forall actor,launch_nonnegative_table(launch_child_tables namespace(namespace_table fork_fixture_world)actor).
Proof.
  intro TABLE;apply child_recording_tables_nonnegative;[exact launch_actual_fork_nonnegative|].
  rewrite TABLE,<-primitive_initial_snapshot;intros fd binding PRESENT.
  exact(primitive_snapshot_nonnegative 0 fd binding PRESENT).
Qed.

Theorem entry_primitive_parent_tables_nonnegative groups program namespace_id ordinal namespace world events ticks
    after_namespace after_world:
  ParentRecording groups program namespace_id fork_fixture_worker_table ordinal namespace world events ticks
    after_namespace after_world ->
  launch_nonnegative_table(namespace_table namespace) ->
  forall actor,launch_nonnegative_table(launch_parent_tables after_namespace fork_fixture_worker_table actor).
Proof.
  intros RUN VALID;apply parent_recording_tables_nonnegative.
  - rewrite <-primitive_initial_snapshot;intros fd binding PRESENT.
    exact(primitive_snapshot_nonnegative 0 fd binding PRESENT).
  - eapply entry_parent_recording_final_nonnegative;[exact RUN|exact VALID].
Qed.
