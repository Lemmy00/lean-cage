(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.acceptance: Record parent descriptor authority on its actual source ticks. *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From compcert Require Import Integers Values.
From LeanImport Require Import Lean.
Require Import Machine LibraryMachine.
From EntryProcess Require Import ProcessMachine ProcessImport ProcessJournal ProcessOwnership
  ProcessSourceRecording ProcessLaunchWitness ProcessLaunchRecordingWitness ProcessParentRecordingWitness
  ProcessChildTickWitness ProcessCapabilityRecording.
From EntryNamespace Require Import NamespaceObjects NamespaceMachine NamespaceKernel NamespacePhysical
  NamespaceCapabilities.
Import ListNotations.
Local Close Scope lean_scope.
Local Open Scope Z_scope.

Lemma parent_recording_tables_nonnegative namespace child:
  launch_nonnegative_table child ->launch_nonnegative_table(namespace_table namespace) ->
  forall actor,launch_nonnegative_table(launch_parent_tables namespace child actor).
Proof.
  intros CHILD PARENT actor;unfold launch_parent_tables;destruct(Nat.eqb actor 1);[exact PARENT|].
  destruct(Nat.eqb actor 2);[exact CHILD|].
  destruct(Nat.eqb actor 3);[exact child_recording_ambient_nonnegative|intros;discriminate].
Qed.

Definition parent_recording_capabilities child namespace:CapabilityWorld:={|
  capability_tables:=launch_parent_tables namespace child;capability_messages:=[]|}.

Lemma parent_recording_tick_observed program ordinal namespace_id child namespace world event after:
  launch_nonnegative_table child ->launch_nonnegative_table(namespace_table namespace) ->
  CapabilityObserved(launch_parent_tick program ordinal namespace_id child world namespace event after)
    (parent_recording_capabilities child namespace).
Proof.
  intros CHILD PARENT actor fd;unfold launch_parent_tick,parent_recording_capabilities;cbn[capability_tables].
  symmetry;apply source_recording_table;apply parent_recording_tables_nonnegative;assumption.
Qed.

Lemma parent_recording_primitive_nonnegative program ordinal namespace_id child namespace world event next after groups:
  SourcePrimitive launch_operation groups launch_recording_child launch_recording_owner(namespace_process event)
    (launch_parent_tick program ordinal namespace_id child world namespace event after)
    {|source_process_before:=world;source_process_after:=after;
      source_namespace_before:=namespace;source_namespace_after:=next|} ->
  launch_nonnegative_table(namespace_table namespace).
Proof.
  intros PRIMITIVE fd binding PRESENT.
  rewrite <-(source_primitive_table _ _ _ _ _ _ _ PRIMITIVE)in PRESENT.
  unfold physical_tick_table in PRESENT;destruct(Z.leb 0(Int.signed fd))eqn:LOW;
    [apply Z.leb_le;exact LOW|discriminate].
Qed.

Lemma parent_recording_capabilities_retable child namespace next:
  capability_retable(parent_recording_capabilities child namespace)1(namespace_table next)=
    parent_recording_capabilities child next.
Proof.
  unfold capability_retable,parent_recording_capabilities;f_equal;apply functional_extensionality;intro actor.
  cbn[capability_tables];unfold task_table_put,launch_parent_tables;destruct(Nat.eqb actor 1);reflexivity.
Qed.

Theorem parent_recording_capability_history groups program namespace_id child ordinal namespace world events ticks
    after_namespace after_world:
  ParentRecording groups program namespace_id child ordinal namespace world events ticks after_namespace after_world ->
  launch_nonnegative_table child ->
  forall runs run prefix suffix native metadata external can_acquire,
    nth_error runs program=Some run ->source_actor run=launch_recording_owner ->
    source_events run=prefix++map namespace_process events++suffix ->length prefix=ordinal ->
  CapabilityHistory launch_operation groups runs native metadata external can_acquire
    launch_recording_owner launch_recording_child(parent_recording_capabilities child namespace)ticks
    (parent_recording_capabilities child after_namespace).
Proof.
  intro RUN;induction RUN;intros CHILD runs run prefix suffix native metadata external can_acquire PROGRAM ACTOR EVENTS LENGTH.
  - constructor.
  - assert(EVENT:nth_error(source_events run)ordinal=Some(namespace_process event)).
    { rewrite <-LENGTH,EVENTS;apply recording_head_event. }
    assert(OBSERVED:CapabilityObserved tick(parent_recording_capabilities child namespace)).
    { unfold tick;apply parent_recording_tick_observed;[exact CHILD|].
      eapply parent_recording_primitive_nonnegative;exact H. }
    assert(AFTER:capability_pending
      (capability_retable (parent_recording_capabilities child namespace)
        (nat_of_Nat (LeanCage_Entry_CallerPhysical_taskKey (source_actor run)))
        (namespace_table next)) [] = parent_recording_capabilities child next).
    { rewrite ACTOR,launch_recording_owner_key,parent_recording_capabilities_retable;reflexivity. }
    eapply capability_history_next with(middle:=parent_recording_capabilities child next);[exact OBSERVED| |].
    + apply recorded_capability_source;eapply source_capability_call with(run:=run)(program:=program)
        (ordinal:=ordinal)(event:=namespace_process event)(retained:=[])(snapshot:=snapshot).
      * exact PROGRAM.
      * exact EVENT.
      * reflexivity.
      * rewrite ACTOR;exact H.
      * reflexivity.
      * exact OBSERVED.
      * apply incl_refl.
      * symmetry;exact AFTER.
    + eapply IHRUN with(run:=run)(prefix:=prefix++[namespace_process event])(suffix:=suffix);try eassumption.
      * rewrite EVENTS;cbn[map];repeat rewrite <-app_assoc;reflexivity.
      * rewrite length_app;cbn;lia.
Qed.
