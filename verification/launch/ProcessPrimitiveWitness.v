(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.origin: Interpret proved primitive data in the same raw kernel history. *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From compcert Require Import Integers Values.
From LeanImport Require Import Lean.
Require Import Machine LibraryMachine.
From EntryProcess Require Import ProcessMachine ProcessImport ProcessJournal ProcessOwnership ProcessPhysicalWitness
  ProcessSourceRecording ProcessScopeRecording ProcessScope ProcessLaunchWitness ProcessLaunchRecordingWitness ProcessParentRecordingWitness ProcessChildTickWitness
  ProcessCapabilityRecording ProcessNativeCapabilities ProcessWorkerOtherWitness ProcessEntryObservations.
From EntryNamespace Require Import NamespaceObjects NamespaceMachine NamespacePhysical NamespaceCapabilities NamespaceHandles.
Import ListNotations.
Local Close Scope lean_scope.

Notation EntryPrimitiveFrame:=LeanCage_Entry_CallerWitness_FDData_Frame.
Definition entry_frame_before(frame:EntryPrimitiveFrame):=
  capability_descriptor_table(LeanCage_Entry_CallerWitness_FDData_objects(LeanCage_Entry_CallerWitness_FDData_Frame_before frame))
    (LeanCage_Entry_CallerWitness_FDData_flags(LeanCage_Entry_CallerWitness_FDData_Frame_before frame)).
Definition entry_frame_after(frame:EntryPrimitiveFrame):=
  capability_descriptor_table(LeanCage_Entry_CallerWitness_FDData_objects(LeanCage_Entry_CallerWitness_FDData_Frame_after frame))
    (LeanCage_Entry_CallerWitness_FDData_flags(LeanCage_Entry_CallerWitness_FDData_Frame_after frame)).

Definition entry_primitive_other_objects(tables:TaskTables)(actor fd:Lean.Nat):=
  physical_objects(tables(nat_of_Nat actor))fd.
Definition entry_primitive_other_flags(tables:TaskTables)(actor fd:Lean.Nat):=
  physical_cloexec(tables(nat_of_Nat actor))fd.
Definition entry_primitive_tick family(tables:TaskTables)before action after frame:=
  LeanCage_Entry_CallerWitness_FDData_tick family launch_recording_child
    (entry_primitive_other_objects tables)(entry_primitive_other_flags tables)before action after frame.

Definition entry_primitive_capabilities(tables:TaskTables)(table:DescriptorTable):CapabilityWorld:={|
  capability_tables:=task_table_put tables 2 table;capability_messages:=[]|}.

Lemma entry_primitive_source family tables before action after frame:
  LeanCage_Entry_CallerPhysical_Tick_source(entry_primitive_tick family tables before action after frame)=
    ProcessImport.Option_none_inst1 LeanCage_Entry_CallerPhysical_SourceReference.
Proof. reflexivity. Qed.

Lemma entry_primitive_label family tables before action after frame:
  LeanCage_Entry_CallerPhysical_Tick_primitive(entry_primitive_tick family tables before action after frame)=
    ProcessImport.Option_some_inst1 LeanCage_Entry_CallerPhysical_PrimitiveLabel
      (LeanCage_Entry_CallerPhysical_PrimitiveLabel_mk family
        (LeanCage_Entry_CallerWitness_FDData_Frame_code frame)ProcessImport.Bool_true).
Proof. reflexivity. Qed.

Lemma entry_primitive_child_objects family tables before action after frame:
  ProcessImport.objects(entry_primitive_tick family tables before action after frame)
    (LeanCage_Entry_CallerPhysical_taskKey launch_recording_child)=
    LeanCage_Entry_CallerWitness_FDData_objects(LeanCage_Entry_CallerWitness_FDData_Frame_before frame).
Proof.
  apply functional_extensionality;intro fd;unfold entry_primitive_tick,LeanCage_Entry_CallerWitness_FDData_tick;
    cbn[ProcessImport.objects].
  rewrite capability_nat_ite_same by reflexivity;reflexivity.
Qed.

Lemma entry_primitive_child_flags family tables before action after frame:
  ProcessImport.cloexec(entry_primitive_tick family tables before action after frame)
    (LeanCage_Entry_CallerPhysical_taskKey launch_recording_child)=
    LeanCage_Entry_CallerWitness_FDData_flags(LeanCage_Entry_CallerWitness_FDData_Frame_before frame).
Proof.
  apply functional_extensionality;intro fd;unfold entry_primitive_tick,LeanCage_Entry_CallerWitness_FDData_tick;
    cbn[ProcessImport.cloexec].
  rewrite capability_nat_ite_same by reflexivity;reflexivity.
Qed.

Theorem entry_primitive_no_socket_write family tables before action after frame actor fd bytes lost:
  ProcessImport.socket(entry_primitive_tick family tables before action after frame)<>
    LeanCage_Entry_CallerPhysical_SocketObservation_wrote actor fd bytes lost.
Proof.
  change(LeanCage_Entry_CallerWitness_FDData_socket launch_recording_child
    (LeanCage_Entry_CallerWitness_FDData_Frame_read frame)<>
      LeanCage_Entry_CallerPhysical_SocketObservation_wrote actor fd bytes lost).
  destruct(LeanCage_Entry_CallerWitness_FDData_Frame_read frame)as[|reading];[discriminate|].
  destruct reading;discriminate.
Qed.

Theorem entry_primitive_placement_recording groups family tables before action after frame:
  (action=LeanCage_Entry_CallerPhysical_Action_native\/
    action=LeanCage_Entry_CallerPhysical_Action_traceMe) ->
  PlacementRecording groups(entry_primitive_tick family tables before action after frame).
Proof. intros[NATIVE|TRACEME]group PLACED;subst action;discriminate PLACED. Qed.

Theorem entry_primitive_frame_step mayTrace family tables context frame:
  LeanCage_Entry_CallerPhysical_Step mayTrace launch_recording_owner launch_recording_child context
    (LeanCage_Entry_CallerPhysical_Tick_action(entry_primitive_tick family tables context
      LeanCage_Entry_CallerPhysical_Action_native context frame))context.
Proof. constructor;reflexivity. Qed.

Lemma entry_encoded_descriptor_table table:
  launch_nonnegative_table table ->
  capability_descriptor_table(physical_objects table)(physical_cloexec table)=table.
Proof.
  intro VALID;apply functional_extensionality;intro fd.
  exact(source_recording_table launch_recording_child 0 0
    (source_recording_context launch_recording_owner false task_running Int64.zero 1 None)
    (source_recording_context launch_recording_owner false task_running Int64.zero 1 None)
    launch_before_fork(namespace_forked(Int.repr 2))(fun _=>table)0 fd(VALID fd)).
Qed.

Theorem entry_primitive_observed family tables before action after frame:
  (forall actor,launch_nonnegative_table(tables actor)) ->
  CapabilityObserved(entry_primitive_tick family tables before action after frame)
    (entry_primitive_capabilities tables(entry_frame_before frame)).
Proof.
  intros VALID actor fd;unfold entry_primitive_capabilities;cbn[capability_tables].
  unfold task_table_put;destruct(Nat.eq_dec actor 2)as[CHILD|OTHER].
  - subst actor;rewrite Nat.eqb_refl.
    unfold physical_tick_table,entry_frame_before.
    assert(KEY:LeanCage_Entry_CallerPhysical_taskKey launch_recording_child=Nat_of_nat 2).
    { pose proof(f_equal Nat_of_nat launch_recording_child_key)as KEY;rewrite Nat2natid in KEY;exact KEY. }
    rewrite <-KEY.
    rewrite entry_primitive_child_objects,entry_primitive_child_flags;reflexivity.
  - assert(NOT_CHILD:Nat_of_nat actor<>LeanCage_Entry_CallerPhysical_taskKey launch_recording_child).
    { intro SAME;apply(f_equal nat_of_Nat)in SAME;rewrite nat2Natid,launch_recording_child_key in SAME;contradiction. }
    assert(NE:Nat.eqb actor 2=false)by(apply Nat.eqb_neq;exact OTHER);rewrite NE.
    unfold physical_tick_table,entry_primitive_tick,LeanCage_Entry_CallerWitness_FDData_tick;
      cbn[ProcessImport.objects ProcessImport.cloexec].
    repeat rewrite capability_nat_ite_other by exact NOT_CHILD.
    unfold entry_primitive_other_objects,entry_primitive_other_flags;rewrite nat2Natid.
    change(tables actor fd=capability_descriptor_table(physical_objects(tables actor))(physical_cloexec(tables actor))fd).
    rewrite entry_encoded_descriptor_table by apply VALID;reflexivity.
Qed.

Theorem entry_primitive_foreign_cgroup family tables before action after frame:
  (forall actor,launch_nonnegative_table(tables actor)) ->
  (forall actor,actor<>1%nat ->actor<>2%nat ->tables actor=entry_foreign_tables actor) ->
  EntryForeignCgroupAbsent(entry_primitive_tick family tables before action after frame).
Proof.
  intros VALID FOREIGN actor OTHER object group CLASS.
  destruct(entry_other_key _ OTHER)as[NOT_PARENT NOT_CHILD].
  assert(NP:nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor)<>1%nat)by(apply Nat.eqb_neq;exact NOT_PARENT).
  assert(NC:nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor)<>2%nat)by(apply Nat.eqb_neq;exact NOT_CHILD).
  eapply entry_foreign_cgroup_observation;[exact OTHER| |exact CLASS].
  apply functional_extensionality;intro fd.
  rewrite <-(entry_primitive_observed _ _ _ _ _ _ VALID _ fd).
  unfold entry_primitive_capabilities;cbn[capability_tables];unfold task_table_put.
  rewrite NOT_CHILD,FOREIGN by assumption;reflexivity.
Qed.

Lemma entry_primitive_after_retable tables frame:
  entry_primitive_capabilities tables(entry_frame_after frame)=
    capability_retable(entry_primitive_capabilities tables(entry_frame_before frame))2(entry_frame_after frame).
Proof.
  unfold entry_primitive_capabilities,capability_retable;cbn[capability_tables capability_messages].
  f_equal;apply functional_extensionality;intro actor;unfold task_table_put;destruct(Nat.eqb actor 2);reflexivity.
Qed.

Definition entry_primitive_descriptor_sample observation ticks family tables before action after frame position:
  (forall actor,launch_nonnegative_table(tables actor)) ->
  nth_error ticks position=Some(entry_primitive_tick family tables before action after frame) ->
  observation position(nat_of_Nat(LeanCage_Entry_CallerWitness_FDData_Frame_code frame))ProcessImport.Bool_true
    (entry_primitive_tick family tables before action after frame)
    (LeanCage_Entry_CallerWitness_FDData_objects(LeanCage_Entry_CallerWitness_FDData_Frame_before frame))
    (LeanCage_Entry_CallerWitness_FDData_flags(LeanCage_Entry_CallerWitness_FDData_Frame_before frame))
    (LeanCage_Entry_CallerWitness_FDData_objects(LeanCage_Entry_CallerWitness_FDData_Frame_after frame))
    (LeanCage_Entry_CallerWitness_FDData_flags(LeanCage_Entry_CallerWitness_FDData_Frame_after frame)) ->
  PrimitiveDescriptorSample observation ticks family 2
    (nat_of_Nat(LeanCage_Entry_CallerWitness_FDData_Frame_code frame))ProcessImport.Bool_true
    (entry_primitive_capabilities tables(entry_frame_before frame))
    (entry_primitive_tick family tables before action after frame)
    (entry_primitive_capabilities tables(entry_frame_after frame)).
Proof.
  intros VALID SELECTED ACTUAL.
  refine{|descriptor_position:=position;
    descriptor_before_objects:=LeanCage_Entry_CallerWitness_FDData_objects(LeanCage_Entry_CallerWitness_FDData_Frame_before frame);
    descriptor_before_flags:=LeanCage_Entry_CallerWitness_FDData_flags(LeanCage_Entry_CallerWitness_FDData_Frame_before frame);
    descriptor_after_objects:=LeanCage_Entry_CallerWitness_FDData_objects(LeanCage_Entry_CallerWitness_FDData_Frame_after frame);
    descriptor_after_flags:=LeanCage_Entry_CallerWitness_FDData_flags(LeanCage_Entry_CallerWitness_FDData_Frame_after frame);
    descriptor_actual:=ACTUAL;descriptor_selected:=SELECTED|}.
  - rewrite Nat2natid;apply entry_primitive_label.
  - apply entry_primitive_observed;exact VALID.
  - rewrite <-launch_recording_child_key,Nat2natid;apply entry_primitive_child_objects.
  - rewrite <-launch_recording_child_key,Nat2natid;apply entry_primitive_child_flags.
  - unfold entry_primitive_capabilities;cbn[capability_tables];apply task_table_put_same.
Defined.

Theorem entry_primitive_native_capability observation ticks tables before action after frame position can_acquire:
  (forall actor,launch_nonnegative_table(tables actor)) ->
  nth_error ticks position=Some(entry_primitive_tick LeanCage_Entry_CallerPhysical_PrimitiveFamily_native
    tables before action after frame) ->
  observation position(nat_of_Nat(LeanCage_Entry_CallerWitness_FDData_Frame_code frame))ProcessImport.Bool_true
    (entry_primitive_tick LeanCage_Entry_CallerPhysical_PrimitiveFamily_native tables before action after frame)
    (LeanCage_Entry_CallerWitness_FDData_objects(LeanCage_Entry_CallerWitness_FDData_Frame_before frame))
    (LeanCage_Entry_CallerWitness_FDData_flags(LeanCage_Entry_CallerWitness_FDData_Frame_before frame))
    (LeanCage_Entry_CallerWitness_FDData_objects(LeanCage_Entry_CallerWitness_FDData_Frame_after frame))
    (LeanCage_Entry_CallerWitness_FDData_flags(LeanCage_Entry_CallerWitness_FDData_Frame_after frame)) ->
  LeanCage_Entry_CallerWitness_DescriptorObjectsFrom
    (LeanCage_Entry_CallerWitness_FDData_objects(LeanCage_Entry_CallerWitness_FDData_Frame_before frame))
    (LeanCage_Entry_CallerWitness_FDData_objects(LeanCage_Entry_CallerWitness_FDData_Frame_after frame)) ->
  RecordedNativeCapability observation ticks can_acquire launch_recording_owner launch_recording_child
    (nat_of_Nat(LeanCage_Entry_CallerWitness_FDData_Frame_code frame))ProcessImport.Bool_true
    (entry_primitive_capabilities tables(entry_frame_before frame))
    (entry_primitive_tick LeanCage_Entry_CallerPhysical_PrimitiveFamily_native tables before action after frame)
    (capability_local 2)(entry_primitive_capabilities tables(entry_frame_after frame)).
Proof.
  intros VALID SELECTED ACTUAL FRAME.
  pose(sample:=entry_primitive_descriptor_sample _ _ _ _ _ _ _ _ _ VALID SELECTED ACTUAL).
  pose proof(@recorded_native_retained observation ticks can_acquire launch_recording_owner launch_recording_child
    (nat_of_Nat(LeanCage_Entry_CallerWitness_FDData_Frame_code frame))ProcessImport.Bool_true
    (entry_primitive_capabilities tables(entry_frame_before frame))
    (entry_primitive_tick LeanCage_Entry_CallerPhysical_PrimitiveFamily_native tables before action after frame)
    (entry_primitive_capabilities tables(entry_frame_after frame)))as BUILD.
  unfold descriptor_child_key in BUILD;rewrite launch_recording_child_key in BUILD.
  eapply BUILD with(sample:=sample);[exact FRAME|apply entry_primitive_after_retable].
Qed.

Theorem entry_primitive_metadata_capability observation ticks tables before action after frame position can_acquire:
  (forall actor,launch_nonnegative_table(tables actor)) ->
  nth_error ticks position=Some(entry_primitive_tick LeanCage_Entry_CallerPhysical_PrimitiveFamily_metadata
    tables before action after frame) ->
  observation position(nat_of_Nat(LeanCage_Entry_CallerWitness_FDData_Frame_code frame))ProcessImport.Bool_true
    (entry_primitive_tick LeanCage_Entry_CallerPhysical_PrimitiveFamily_metadata tables before action after frame)
    (LeanCage_Entry_CallerWitness_FDData_objects(LeanCage_Entry_CallerWitness_FDData_Frame_before frame))
    (LeanCage_Entry_CallerWitness_FDData_flags(LeanCage_Entry_CallerWitness_FDData_Frame_before frame))
    (LeanCage_Entry_CallerWitness_FDData_objects(LeanCage_Entry_CallerWitness_FDData_Frame_after frame))
    (LeanCage_Entry_CallerWitness_FDData_flags(LeanCage_Entry_CallerWitness_FDData_Frame_after frame)) ->
  LeanCage_Entry_CallerWitness_DescriptorCapabilityEffect
    (LeanCage_Entry_CallerWitness_FDData_objects(LeanCage_Entry_CallerWitness_FDData_Frame_before frame))
    (LeanCage_Entry_CallerWitness_FDData_objects(LeanCage_Entry_CallerWitness_FDData_Frame_after frame))
    (LeanCage_Entry_CallerWitness_FDData_flags(LeanCage_Entry_CallerWitness_FDData_Frame_before frame))
    (LeanCage_Entry_CallerWitness_FDData_flags(LeanCage_Entry_CallerWitness_FDData_Frame_after frame)) ->
  exists effect,RecordedMetadataCapability observation ticks can_acquire launch_recording_owner launch_recording_child
    (nat_of_Nat(LeanCage_Entry_CallerWitness_FDData_Frame_code frame))ProcessImport.Bool_true
    (entry_primitive_capabilities tables(entry_frame_before frame))
    (entry_primitive_tick LeanCage_Entry_CallerPhysical_PrimitiveFamily_metadata tables before action after frame)
    effect(entry_primitive_capabilities tables(entry_frame_after frame)).
Proof.
  intros VALID SELECTED ACTUAL FRAME.
  pose(sample:=entry_primitive_descriptor_sample _ _ _ _ _ _ _ _ _ VALID SELECTED ACTUAL).
  pose proof(@recorded_metadata_capability_from_sample observation ticks can_acquire launch_recording_owner launch_recording_child
    (nat_of_Nat(LeanCage_Entry_CallerWitness_FDData_Frame_code frame))ProcessImport.Bool_true
    (entry_primitive_capabilities tables(entry_frame_before frame))
    (entry_primitive_tick LeanCage_Entry_CallerPhysical_PrimitiveFamily_metadata tables before action after frame)
    (entry_primitive_capabilities tables(entry_frame_after frame)))as BUILD.
  unfold descriptor_child_key in BUILD;rewrite launch_recording_child_key in BUILD.
  eapply BUILD with(sample:=sample);[exact FRAME|apply entry_primitive_after_retable].
Qed.
