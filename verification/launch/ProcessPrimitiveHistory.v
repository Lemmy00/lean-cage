(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.origin: Retain the actual primitive at its fixed global position. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Integers Values.
From LeanImport Require Import Lean.
Require Import Machine LibraryMachine.
From EntryProcess Require Import ProcessMachine ProcessImport ProcessJournal ProcessOwnership ProcessPhysicalWitness ProcessCallerConnection
  ProcessSourceRecording ProcessLaunchWitness ProcessLaunchRecordingWitness ProcessParentRecordingWitness ProcessChildTickWitness
  ProcessCapabilityRecording ProcessNativeCapabilities ProcessPrimitiveWitness ProcessPrimitiveData ProcessPrimitiveRuns.
From EntryNamespace Require Import NamespaceObjects NamespacePhysical NamespaceCapabilities.
Import ListNotations.
Local Close Scope lean_scope.
Local Open Scope nat_scope.

Definition PrimitivePlan:=list(option(LeanCage_Entry_CallerPhysical_PrimitiveFamily*EntryPrimitiveFrame)).
Definition primitive_plan family frames:PrimitivePlan:=map(fun frame=>Some(family,frame))frames.

Definition primitive_prefix_plan:PrimitivePlan:=
  primitive_plan LeanCage_Entry_CallerPhysical_PrimitiveFamily_metadata
    (primitive_frames LeanCage_Entry_CallerWitness_FDData_inspectionFrames)++
  primitive_plan LeanCage_Entry_CallerPhysical_PrimitiveFamily_metadata
    (primitive_frames LeanCage_Entry_CallerWitness_FDData_inspectionFrames)++
  primitive_plan LeanCage_Entry_CallerPhysical_PrimitiveFamily_native
    (primitive_frames LeanCage_Entry_CallerWitness_FDData_signalFrames)++
  primitive_plan LeanCage_Entry_CallerPhysical_PrimitiveFamily_native[primitive_pack 2 0 0;primitive_pack 3 0 0].
Definition primitive_tail_plan:PrimitivePlan:=
  primitive_plan LeanCage_Entry_CallerPhysical_PrimitiveFamily_native
    (primitive_frames LeanCage_Entry_CallerWitness_FDData_tailFrames++[primitive_pack 23 6 7]).

Definition entry_primitive_plan(child_count parent_count:nat):PrimitivePlan:=
  repeat None child_count++primitive_prefix_plan++repeat None parent_count++primitive_tail_plan.

Definition entry_descriptor_observation(plan:PrimitivePlan)family:PrimitiveDescriptorObservation:=
  fun position code origin tick before_objects before_flags after_objects after_flags=>
  exists frame,nth_error plan position=Some(Some(family,frame)) /\
    code=primitive_frame_code frame /\origin=ProcessImport.Bool_true /\
    before_objects=LeanCage_Entry_CallerWitness_FDData_objects(LeanCage_Entry_CallerWitness_FDData_Frame_before frame) /\
    before_flags=LeanCage_Entry_CallerWitness_FDData_flags(LeanCage_Entry_CallerWitness_FDData_Frame_before frame) /\
    after_objects=LeanCage_Entry_CallerWitness_FDData_objects(LeanCage_Entry_CallerWitness_FDData_Frame_after frame) /\
    after_flags=LeanCage_Entry_CallerWitness_FDData_flags(LeanCage_Entry_CallerWitness_FDData_Frame_after frame).

Lemma primitive_plan_head prefix family frame frames suffix:
  nth_error(prefix++primitive_plan family(frame::frames)++suffix)(length prefix)=Some(Some(family,frame)).
Proof. unfold primitive_plan;cbn[map];rewrite nth_error_app2 by lia;rewrite Nat.sub_diag;reflexivity. Qed.

Lemma primitive_plan_selected prefix family frames suffix index frame:
  nth_error frames index=Some frame ->
  nth_error(prefix++primitive_plan family frames++suffix)(length prefix+index)=Some(Some(family,frame)).
Proof.
  intro SELECTED;rewrite nth_error_app2 by lia.
  replace(length prefix+index-length prefix)with index by lia.
  rewrite nth_error_app1.
  - unfold primitive_plan;rewrite nth_error_map,SELECTED;reflexivity.
  - unfold primitive_plan;rewrite length_map;apply nth_error_Some;rewrite SELECTED;discriminate.
Qed.

Lemma entry_descriptor_observed plan family position frame tick:
  nth_error plan position=Some(Some(family,frame)) ->
  entry_descriptor_observation plan family position(primitive_frame_code frame)ProcessImport.Bool_true tick
    (LeanCage_Entry_CallerWitness_FDData_objects(LeanCage_Entry_CallerWitness_FDData_Frame_before frame))
    (LeanCage_Entry_CallerWitness_FDData_flags(LeanCage_Entry_CallerWitness_FDData_Frame_before frame))
    (LeanCage_Entry_CallerWitness_FDData_objects(LeanCage_Entry_CallerWitness_FDData_Frame_after frame))
    (LeanCage_Entry_CallerWitness_FDData_flags(LeanCage_Entry_CallerWitness_FDData_Frame_after frame)).
Proof. intro SELECTED;exists frame;repeat split;try exact SELECTED;reflexivity. Qed.

Inductive PrimitiveTableChain:DescriptorTable->list EntryPrimitiveFrame->DescriptorTable->Prop:=
| primitive_table_done:forall table,PrimitiveTableChain table[]table
| primitive_table_next:forall frame frames last,
    PrimitiveTableChain(entry_frame_after frame)frames last ->
    PrimitiveTableChain(entry_frame_before frame)(frame::frames)last.

Lemma primitive_global_tick prefix family tables context frame frames suffix:
  nth_error(prefix++entry_primitive_ticks family tables context(frame::frames)++suffix)(length prefix)=
    Some(entry_primitive_tick family tables context LeanCage_Entry_CallerPhysical_Action_native context frame).
Proof. unfold entry_primitive_ticks;cbn[map];rewrite nth_error_app2 by lia;rewrite Nat.sub_diag;reflexivity. Qed.

Theorem entry_native_frame_history observation global_ticks tables context frames first last:
  PrimitiveTableChain first frames last ->
  (forall actor,launch_nonnegative_table(tables actor)) ->
  LeanCage_Entry_CallerPhysical_ContextSafe launch_recording_owner context ->
  (forall frame,In frame frames ->LeanCage_Entry_CallerPhysical_LocalEntryCode
    (LeanCage_Entry_CallerWitness_FDData_Frame_code frame)) ->
  (forall frame,In frame frames ->LeanCage_Entry_CallerWitness_DescriptorObjectsFrom
    (LeanCage_Entry_CallerWitness_FDData_objects(LeanCage_Entry_CallerWitness_FDData_Frame_before frame))
    (LeanCage_Entry_CallerWitness_FDData_objects(LeanCage_Entry_CallerWitness_FDData_Frame_after frame))) ->
  forall prefix suffix can_acquire metadata external runs,
    global_ticks=prefix++entry_primitive_ticks LeanCage_Entry_CallerPhysical_PrimitiveFamily_native tables context frames++suffix ->
    (forall index frame,nth_error frames index=Some frame ->
      observation(length prefix+index)(primitive_frame_code frame)ProcessImport.Bool_true
        (entry_primitive_tick LeanCage_Entry_CallerPhysical_PrimitiveFamily_native tables context
          LeanCage_Entry_CallerPhysical_Action_native context frame)
        (LeanCage_Entry_CallerWitness_FDData_objects(LeanCage_Entry_CallerWitness_FDData_Frame_before frame))
        (LeanCage_Entry_CallerWitness_FDData_flags(LeanCage_Entry_CallerWitness_FDData_Frame_before frame))
        (LeanCage_Entry_CallerWitness_FDData_objects(LeanCage_Entry_CallerWitness_FDData_Frame_after frame))
        (LeanCage_Entry_CallerWitness_FDData_flags(LeanCage_Entry_CallerWitness_FDData_Frame_after frame))) ->
  CapabilityHistory launch_operation launch_group_objects runs
    (RecordedNativeCapability observation global_ticks can_acquire launch_recording_owner launch_recording_child)
    metadata external can_acquire launch_recording_owner launch_recording_child
    (entry_primitive_capabilities tables first)
    (entry_primitive_ticks LeanCage_Entry_CallerPhysical_PrimitiveFamily_native tables context frames)
    (entry_primitive_capabilities tables last).
Proof.
  intro CHAIN;induction CHAIN;intros VALID SAFE CODES FRAMES prefix suffix can_acquire metadata external runs TICKS OBSERVATIONS.
  - constructor.
  - cbn[entry_primitive_ticks map].
    eapply capability_history_next.
    + apply entry_primitive_observed;exact VALID.
    + eapply recorded_capability_native with(code:=primitive_frame_code frame)(origin:=ProcessImport.Bool_true)
        (action:=capability_local 2).
      * eapply entry_primitive_native_capability with(position:=length prefix);[exact VALID| | |apply FRAMES;left;reflexivity].
        -- rewrite TICKS;apply primitive_global_tick.
        -- replace(length prefix)with(length prefix+0)by lia;apply OBSERVATIONS;reflexivity.
      * exact SAFE.
      * reflexivity.
      * unfold primitive_frame_code;rewrite Nat2natid;apply CODES;left;reflexivity.
    + eapply IHCHAIN with(prefix:=prefix++[entry_primitive_tick LeanCage_Entry_CallerPhysical_PrimitiveFamily_native
        tables context LeanCage_Entry_CallerPhysical_Action_native context frame])(suffix:=suffix).
      * exact VALID.
      * exact SAFE.
      * intros actual MEMBER;apply CODES;right;exact MEMBER.
      * intros actual MEMBER;apply FRAMES;right;exact MEMBER.
      * rewrite TICKS;unfold entry_primitive_ticks;cbn[map];repeat rewrite <-app_assoc;reflexivity.
      * intros index actual SELECTED;rewrite length_app;cbn[length].
        replace(length prefix+1+index)with(length prefix+S index)by lia.
        apply OBSERVATIONS;exact SELECTED.
Qed.

Definition primitive_snapshot_table index:=
  capability_descriptor_table(LeanCage_Entry_CallerWitness_FDData_objects(primitive_snapshot index))
    (LeanCage_Entry_CallerWitness_FDData_flags(primitive_snapshot index)).

Lemma primitive_local_code frame:
  primitive_frame_code frame<=27 ->
  LeanCage_Entry_CallerPhysical_LocalEntryCode(LeanCage_Entry_CallerWitness_FDData_Frame_code frame).
Proof. intro BOUND;unfold LeanCage_Entry_CallerPhysical_LocalEntryCode;apply nat_le_Nat_le;exact BOUND. Qed.

Lemma primitive_context_untraced_safe:
  LeanCage_Entry_CallerPhysical_ContextSafe launch_recording_owner
    (primitive_context false task_running Int64.zero None).
Proof. apply Lean.Or_inl;constructor. Qed.

Lemma primitive_context_traced_safe:
  LeanCage_Entry_CallerPhysical_ContextSafe launch_recording_owner
    (primitive_context true task_running Int64.zero None).
Proof. apply Lean.Or_inr;constructor;[constructor|constructor;[constructor|apply Lean.Or_inl;constructor]]. Qed.

Lemma primitive_context_released_safe:
  LeanCage_Entry_CallerPhysical_ContextSafe launch_recording_owner
    (primitive_context true task_running(Int64.repr 1048592)(Some 1)).
Proof.
  apply Lean.Or_inr;constructor;[constructor|constructor].
  - constructor;[apply Lean.Or_inr,Lean.Or_inl;constructor|].
    constructor;[apply Lean.Or_inl;constructor|constructor].
  - change(LeanCage_Entry_TracerOptionsAllowed(caller_options_nat(Int64.repr 1048592))).
    apply caller_options_word_ordinary_Lean;reflexivity.
Qed.

Lemma primitive_table_chain_constant frames table:
  (forall frame,In frame frames ->entry_frame_before frame=table /\entry_frame_after frame=table) ->
  PrimitiveTableChain table frames table.
Proof.
  induction frames as[|frame frames IH];intro SAME;[constructor|].
  destruct(SAME frame(or_introl(Logic.eq_refl _)))as[BEFORE AFTER].
  assert(REST:PrimitiveTableChain(entry_frame_after frame)frames table).
  { rewrite AFTER;apply IH;intros actual MEMBER;apply SAME;right;exact MEMBER. }
  pose proof(primitive_table_next frame frames table REST)as STEP;rewrite BEFORE in STEP;exact STEP.
Qed.

Lemma primitive_inspection_table_chain:
  PrimitiveTableChain(primitive_snapshot_table 0)
    (primitive_frames LeanCage_Entry_CallerWitness_FDData_inspectionFrames)(primitive_snapshot_table 0).
Proof.
  change(PrimitiveTableChain(entry_frame_before(primitive_pack 0 0 1))
    [primitive_pack 0 0 1;primitive_pack 1 1 1;primitive_pack 1 1 1;primitive_pack 2 1 0]
    (entry_frame_after(primitive_pack 2 1 0))).
  apply(primitive_table_next(primitive_pack 0 0 1)).
  apply(primitive_table_next(primitive_pack 1 1 1)).
  apply(primitive_table_next(primitive_pack 1 1 1)).
  apply(primitive_table_next(primitive_pack 2 1 0)).
  apply primitive_table_done.
Qed.

Lemma primitive_signal_table_chain:
  PrimitiveTableChain(primitive_snapshot_table 0)
    (primitive_frames LeanCage_Entry_CallerWitness_FDData_signalFrames)(primitive_snapshot_table 0).
Proof.
  apply primitive_table_chain_constant;intros frame MEMBER;rewrite primitive_signal_values in MEMBER.
  destruct MEMBER as[FRAME|MEMBER];[subst frame;split;reflexivity|].
  apply in_app_or in MEMBER;destruct MEMBER as[MEMBER|[FRAME|EMPTY]];try contradiction.
  - apply repeat_spec in MEMBER;subst frame;split;reflexivity.
  - subst frame;split;reflexivity.
Qed.

Lemma primitive_table_chain_append first left middle right last:
  PrimitiveTableChain first left middle ->PrimitiveTableChain middle right last ->
  PrimitiveTableChain first(left++right)last.
Proof. intros CHAIN;induction CHAIN;intro REST;cbn;[exact REST|constructor;apply IHCHAIN;exact REST]. Qed.

Lemma primitive_tail_table_chain:
  PrimitiveTableChain(primitive_snapshot_table 0)
    (primitive_frames LeanCage_Entry_CallerWitness_FDData_tailFrames++[primitive_pack 23 6 7])
    (primitive_snapshot_table 7).
Proof.
  rewrite primitive_tail_exact;unfold primitive_tail_values;rewrite <-app_assoc.
  change(PrimitiveTableChain(entry_frame_before primitive_read_frame)
    ([primitive_read_frame;primitive_pack 4 0 2;primitive_pack 4 2 3;primitive_pack 4 3 4;
      primitive_pack 5 4 5;primitive_pack 6 5 6]++
      map(fun code=>primitive_pack code 6 6)ProcessPrimitiveData.primitive_tail_codes++[primitive_pack 23 6 7])
      (primitive_snapshot_table 7)).
  cbn[app];apply(primitive_table_next primitive_read_frame).
  apply(primitive_table_next(primitive_pack 4 0 2)).
  apply(primitive_table_next(primitive_pack 4 2 3)).
  apply(primitive_table_next(primitive_pack 4 3 4)).
  apply(primitive_table_next(primitive_pack 5 4 5)).
  apply(primitive_table_next(primitive_pack 6 5 6)).
  eapply primitive_table_chain_append with(middle:=primitive_snapshot_table 6).
  - apply primitive_table_chain_constant;intros frame MEMBER;apply in_map_iff in MEMBER.
    destruct MEMBER as[code[SAME MEMBER]];subst frame;split;reflexivity.
  - change(PrimitiveTableChain(entry_frame_before(primitive_pack 23 6 7))[primitive_pack 23 6 7]
      (entry_frame_after(primitive_pack 23 6 7))).
    apply(primitive_table_next(primitive_pack 23 6 7));apply primitive_table_done.
Qed.

Theorem entry_metadata_frame_history observation global_ticks tables context frames first last:
  PrimitiveTableChain first frames last ->
  (forall actor,launch_nonnegative_table(tables actor)) ->
  LeanCage_Entry_CallerPhysical_ContextSafe launch_recording_owner context ->
  (forall frame,In frame frames ->primitive_metadata_frame frame) ->
  (forall frame,In frame frames ->LeanCage_Entry_CallerWitness_DescriptorCapabilityEffect
    (LeanCage_Entry_CallerWitness_FDData_objects(LeanCage_Entry_CallerWitness_FDData_Frame_before frame))
    (LeanCage_Entry_CallerWitness_FDData_objects(LeanCage_Entry_CallerWitness_FDData_Frame_after frame))
    (LeanCage_Entry_CallerWitness_FDData_flags(LeanCage_Entry_CallerWitness_FDData_Frame_before frame))
    (LeanCage_Entry_CallerWitness_FDData_flags(LeanCage_Entry_CallerWitness_FDData_Frame_after frame))) ->
  forall prefix suffix can_acquire native external runs,
    global_ticks=prefix++entry_primitive_ticks LeanCage_Entry_CallerPhysical_PrimitiveFamily_metadata tables context frames++suffix ->
    (forall index frame,nth_error frames index=Some frame ->
      observation(length prefix+index)(primitive_frame_code frame)ProcessImport.Bool_true
        (entry_primitive_tick LeanCage_Entry_CallerPhysical_PrimitiveFamily_metadata tables context
          LeanCage_Entry_CallerPhysical_Action_native context frame)
        (LeanCage_Entry_CallerWitness_FDData_objects(LeanCage_Entry_CallerWitness_FDData_Frame_before frame))
        (LeanCage_Entry_CallerWitness_FDData_flags(LeanCage_Entry_CallerWitness_FDData_Frame_before frame))
        (LeanCage_Entry_CallerWitness_FDData_objects(LeanCage_Entry_CallerWitness_FDData_Frame_after frame))
        (LeanCage_Entry_CallerWitness_FDData_flags(LeanCage_Entry_CallerWitness_FDData_Frame_after frame))) ->
  CapabilityHistory launch_operation launch_group_objects runs native
    (RecordedMetadataCapability observation global_ticks can_acquire launch_recording_owner launch_recording_child)
    external can_acquire launch_recording_owner launch_recording_child
    (entry_primitive_capabilities tables first)
    (entry_primitive_ticks LeanCage_Entry_CallerPhysical_PrimitiveFamily_metadata tables context frames)
    (entry_primitive_capabilities tables last).
Proof.
  intro CHAIN;induction CHAIN;intros VALID SAFE CODES FRAMES prefix suffix can_acquire native external runs TICKS OBSERVATIONS.
  - constructor.
  - cbn[entry_primitive_ticks map].
    destruct(entry_primitive_metadata_capability observation global_ticks tables context
      LeanCage_Entry_CallerPhysical_Action_native context frame(length prefix)can_acquire VALID
      ltac:(rewrite TICKS;apply primitive_global_tick)
      ltac:(replace(length prefix)with(length prefix+0)by lia;apply OBSERVATIONS;reflexivity)
      (FRAMES frame(or_introl(Logic.eq_refl _))))as[action OPERATION].
    eapply capability_history_next.
    + apply entry_primitive_observed;exact VALID.
    + eapply recorded_capability_metadata with(code:=primitive_frame_code frame)(origin:=ProcessImport.Bool_true)
        (action:=action);[exact OPERATION|exact SAFE|reflexivity|apply CODES;left;reflexivity].
    + eapply IHCHAIN with(prefix:=prefix++[entry_primitive_tick LeanCage_Entry_CallerPhysical_PrimitiveFamily_metadata
        tables context LeanCage_Entry_CallerPhysical_Action_native context frame])(suffix:=suffix).
      * exact VALID.
      * exact SAFE.
      * intros actual MEMBER;apply CODES;right;exact MEMBER.
      * intros actual MEMBER;apply FRAMES;right;exact MEMBER.
      * rewrite TICKS;unfold entry_primitive_ticks;cbn[map];repeat rewrite <-app_assoc;reflexivity.
      * intros index actual SELECTED;rewrite length_app;cbn[length].
        replace(length prefix+1+index)with(length prefix+S index)by lia.
        apply OBSERVATIONS;exact SELECTED.
Qed.

Theorem entry_native_plan_history plan global_ticks tables context frames first last:
  PrimitiveTableChain first frames last ->
  (forall actor,launch_nonnegative_table(tables actor)) ->
  LeanCage_Entry_CallerPhysical_ContextSafe launch_recording_owner context ->
  (forall frame,In frame frames ->primitive_frame_code frame<=27) ->
  (forall frame,In frame frames ->PrimitiveRetained frame) ->
  forall prefix suffix plan_prefix plan_suffix can_acquire metadata external runs,
    global_ticks=prefix++entry_primitive_ticks LeanCage_Entry_CallerPhysical_PrimitiveFamily_native tables context frames++suffix ->
    plan=plan_prefix++primitive_plan LeanCage_Entry_CallerPhysical_PrimitiveFamily_native frames++plan_suffix ->
    length plan_prefix=length prefix ->
    CapabilityHistory launch_operation launch_group_objects runs
      (RecordedNativeCapability(entry_descriptor_observation plan LeanCage_Entry_CallerPhysical_PrimitiveFamily_native)
        global_ticks can_acquire launch_recording_owner launch_recording_child)
      metadata external can_acquire launch_recording_owner launch_recording_child
      (entry_primitive_capabilities tables first)
      (entry_primitive_ticks LeanCage_Entry_CallerPhysical_PrimitiveFamily_native tables context frames)
      (entry_primitive_capabilities tables last).
Proof.
  intros CHAIN VALID SAFE CODES EFFECTS prefix suffix plan_prefix plan_suffix can_acquire metadata external runs
    TICKS PLAN LENGTH.
  eapply entry_native_frame_history with(prefix:=prefix)(suffix:=suffix);try eassumption.
  - intros frame MEMBER;apply primitive_local_code,CODES;exact MEMBER.
  - intros frame MEMBER;exact(primitive_retained_data _ (EFFECTS frame MEMBER)).
  - intros index frame SELECTED;apply entry_descriptor_observed;rewrite PLAN,<-LENGTH.
    apply primitive_plan_selected;exact SELECTED.
Qed.

Theorem entry_metadata_plan_history plan global_ticks tables context frames first last:
  PrimitiveTableChain first frames last ->
  (forall actor,launch_nonnegative_table(tables actor)) ->
  LeanCage_Entry_CallerPhysical_ContextSafe launch_recording_owner context ->
  (forall frame,In frame frames ->primitive_metadata_frame frame) ->
  (forall frame,In frame frames ->PrimitiveInspection frame) ->
  forall prefix suffix plan_prefix plan_suffix can_acquire native external runs,
    global_ticks=prefix++entry_primitive_ticks LeanCage_Entry_CallerPhysical_PrimitiveFamily_metadata tables context frames++suffix ->
    plan=plan_prefix++primitive_plan LeanCage_Entry_CallerPhysical_PrimitiveFamily_metadata frames++plan_suffix ->
    length plan_prefix=length prefix ->
    CapabilityHistory launch_operation launch_group_objects runs native
      (RecordedMetadataCapability(entry_descriptor_observation plan LeanCage_Entry_CallerPhysical_PrimitiveFamily_metadata)
        global_ticks can_acquire launch_recording_owner launch_recording_child)
      external can_acquire launch_recording_owner launch_recording_child
      (entry_primitive_capabilities tables first)
      (entry_primitive_ticks LeanCage_Entry_CallerPhysical_PrimitiveFamily_metadata tables context frames)
      (entry_primitive_capabilities tables last).
Proof.
  intros CHAIN VALID SAFE CODES EFFECTS prefix suffix plan_prefix plan_suffix can_acquire native external runs
    TICKS PLAN LENGTH.
  eapply entry_metadata_frame_history with(prefix:=prefix)(suffix:=suffix);try eassumption.
  - intros frame MEMBER;exact(primitive_inspection_data _ (EFFECTS frame MEMBER)).
  - intros index frame SELECTED;apply entry_descriptor_observed;rewrite PLAN,<-LENGTH.
    apply primitive_plan_selected;exact SELECTED.
Qed.

Definition entry_runtime_ticks child_ticks parent_ticks prefix_tables tail_tables:=
  child_ticks++entry_worker_prefix prefix_tables++parent_ticks++entry_worker_tail tail_tables.
Definition entry_runtime_native child_ticks parent_ticks prefix_tables tail_tables can_acquire:=
  RecordedNativeCapability
    (entry_descriptor_observation(entry_primitive_plan(length child_ticks)(length parent_ticks))
      LeanCage_Entry_CallerPhysical_PrimitiveFamily_native)
    (entry_runtime_ticks child_ticks parent_ticks prefix_tables tail_tables)can_acquire
    launch_recording_owner launch_recording_child.

Theorem entry_native_singleton_plan_history plan global_ticks tables before action after frame
    prefix suffix plan_prefix plan_suffix can_acquire metadata external runs:
  (forall actor,launch_nonnegative_table(tables actor)) ->
  LeanCage_Entry_CallerPhysical_ContextSafe launch_recording_owner before ->
  primitive_frame_code frame<=27 ->PrimitiveRetained frame ->
  global_ticks=prefix++[entry_primitive_tick LeanCage_Entry_CallerPhysical_PrimitiveFamily_native
    tables before action after frame]++suffix ->
  plan=plan_prefix++primitive_plan LeanCage_Entry_CallerPhysical_PrimitiveFamily_native[frame]++plan_suffix ->
  length plan_prefix=length prefix ->
  CapabilityHistory launch_operation launch_group_objects runs
    (RecordedNativeCapability(entry_descriptor_observation plan LeanCage_Entry_CallerPhysical_PrimitiveFamily_native)
      global_ticks can_acquire launch_recording_owner launch_recording_child)
    metadata external can_acquire launch_recording_owner launch_recording_child
    (entry_primitive_capabilities tables(entry_frame_before frame))
    [entry_primitive_tick LeanCage_Entry_CallerPhysical_PrimitiveFamily_native tables before action after frame]
    (entry_primitive_capabilities tables(entry_frame_after frame)).
Proof.
  intros VALID SAFE CODE EFFECT TICKS PLAN LENGTH.
  eapply capability_history_next;[apply entry_primitive_observed;exact VALID| |constructor].
  eapply recorded_capability_native with(code:=primitive_frame_code frame)(origin:=ProcessImport.Bool_true)
    (action:=capability_local 2).
  - eapply entry_primitive_native_capability with(position:=length prefix);[exact VALID| | |exact(primitive_retained_data _ EFFECT)].
    + rewrite TICKS;apply recording_head_event.
    + apply entry_descriptor_observed;rewrite PLAN,<-LENGTH;apply primitive_plan_head.
  - exact SAFE.
  - reflexivity.
  - unfold primitive_frame_code;rewrite Nat2natid;apply primitive_local_code;exact CODE.
Qed.
Definition entry_runtime_metadata child_ticks parent_ticks prefix_tables tail_tables can_acquire:=
  RecordedMetadataCapability
    (entry_descriptor_observation(entry_primitive_plan(length child_ticks)(length parent_ticks))
      LeanCage_Entry_CallerPhysical_PrimitiveFamily_metadata)
    (entry_runtime_ticks child_ticks parent_ticks prefix_tables tail_tables)can_acquire
    launch_recording_owner launch_recording_child.

Lemma primitive_prefix_plan_length:length primitive_prefix_plan=74.
Proof. unfold primitive_prefix_plan,primitive_plan;repeat rewrite length_app;repeat rewrite length_map;reflexivity. Qed.

Theorem entry_worker_tail_capabilities child_ticks parent_ticks prefix_tables tail_tables can_acquire external runs:
  (forall actor,launch_nonnegative_table(tail_tables actor)) ->
  CapabilityHistory launch_operation launch_group_objects runs
    (entry_runtime_native child_ticks parent_ticks prefix_tables tail_tables can_acquire)
    (entry_runtime_metadata child_ticks parent_ticks prefix_tables tail_tables can_acquire)
    external can_acquire launch_recording_owner launch_recording_child
    (entry_primitive_capabilities tail_tables(primitive_snapshot_table 0))
    (entry_worker_tail tail_tables)
    (entry_primitive_capabilities tail_tables(primitive_snapshot_table 7)).
Proof.
  intro VALID;unfold entry_runtime_native,entry_worker_tail.
  eapply entry_native_plan_history with
    (prefix:=child_ticks++entry_worker_prefix prefix_tables++parent_ticks)(suffix:=[])
    (plan_prefix:=repeat None(length child_ticks)++primitive_prefix_plan++repeat None(length parent_ticks))
    (plan_suffix:=[]).
  - exact primitive_tail_table_chain.
  - exact VALID.
  - exact primitive_context_released_safe.
  - intros frame MEMBER;apply in_app_or in MEMBER;destruct MEMBER as[MEMBER|[SAME|EMPTY]];try contradiction.
    + apply primitive_tail_code;exact MEMBER.
    + subst frame;change(23<=27);lia.
  - intros frame MEMBER;apply in_app_or in MEMBER;destruct MEMBER as[MEMBER|[SAME|EMPTY]];try contradiction.
    + apply primitive_tail_retained;exact MEMBER.
    + subst frame;exact primitive_exec_retained.
  - unfold entry_runtime_ticks,entry_worker_tail;rewrite app_nil_r;repeat rewrite <-app_assoc;reflexivity.
  - unfold entry_primitive_plan,primitive_tail_plan;rewrite app_nil_r;repeat rewrite <-app_assoc;reflexivity.
  - repeat rewrite length_app;repeat rewrite repeat_length.
    rewrite primitive_prefix_plan_length,entry_worker_prefix_length;lia.
Qed.
