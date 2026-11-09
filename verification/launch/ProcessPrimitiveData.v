(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.acceptance: Check the exact descriptor data of the actual ordinary worker slices. *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From compcert Require Import Integers Values.
From LeanImport Require Import Lean.
From EntryProcess Require Import ProcessImport ProcessNativeCapabilities.
From EntryNamespace Require Import NamespaceObjects NamespaceHandles NamespacePhysical NamespaceForkWorldWitness
  NamespaceChildWorldWitness.
Import ListNotations.
Local Close Scope lean_scope.
Local Open Scope Z_scope.
Local Notation PrimitiveFrame:=LeanCage_Entry_CallerWitness_FDData_Frame.
Local Notation PrimitiveSlots:=(ProcessImport.List_inst1 LeanCage_Entry_CallerWitness_FDData_Slot).
Local Notation frame_before:=LeanCage_Entry_CallerWitness_FDData_Frame_before.
Local Notation frame_after:=LeanCage_Entry_CallerWitness_FDData_Frame_after.
Local Notation frame_code:=LeanCage_Entry_CallerWitness_FDData_Frame_code.
Local Notation data_objects:=LeanCage_Entry_CallerWitness_FDData_objects.
Local Notation data_flags:=LeanCage_Entry_CallerWitness_FDData_flags.

Fixpoint primitive_frames(values:ProcessImport.List_inst1 PrimitiveFrame):list PrimitiveFrame:=match values with
  |ProcessImport.List_nil_inst1 _=>[]|ProcessImport.List_cons_inst1 _ frame rest=>frame::primitive_frames rest end.
Definition primitive_snapshot(index:nat):PrimitiveSlots:=
  LeanCage_Entry_CallerWitness_FDData_atD PrimitiveSlots
    (ProcessImport.List_nil_inst1 LeanCage_Entry_CallerWitness_FDData_Slot)
    LeanCage_Entry_CallerWitness_FDData_snapshots(Nat_of_nat index).
Definition primitive_pack(code before after:nat):PrimitiveFrame:=
  LeanCage_Entry_CallerWitness_FDData_pack(Nat_of_nat code)(Nat_of_nat before)(Nat_of_nat after)
    (ProcessImport.Option_none_inst1(ProcessImport.Prod_inst3 Lean.Nat(ProcessImport.List_inst1 Lean.Nat))).

Lemma primitive_objects_outside slots fd:
  nat_of_Nat fd<>0%nat ->nat_of_Nat fd<>1%nat ->nat_of_Nat fd<>2%nat ->nat_of_Nat fd<>3%nat ->
  nat_of_Nat fd<>4%nat ->nat_of_Nat fd<>5%nat ->nat_of_Nat fd<>6%nat ->nat_of_Nat fd<>60%nat ->
  data_objects slots fd=ProcessImport.Option_none_inst1 Lean.Nat.
Proof.
  intros ZERO ONE TWO THREE FOUR FIVE SIX SIXTY.
  unfold LeanCage_Entry_CallerWitness_FDData_objects,LeanCage_Entry_CallerWitness_FDData_lookup.
  repeat rewrite capability_nat_ite_other by
    (intro SAME;subst fd;first[
      solve[apply ZERO;reflexivity]|solve[apply ONE;reflexivity]|solve[apply TWO;reflexivity]|
      solve[apply THREE;reflexivity]|solve[apply FOUR;reflexivity]|solve[apply FIVE;reflexivity]|
      solve[apply SIX;reflexivity]|solve[apply SIXTY;reflexivity]]).
  reflexivity.
Qed.

Lemma primitive_flags_outside slots fd:
  nat_of_Nat fd<>0%nat ->nat_of_Nat fd<>1%nat ->nat_of_Nat fd<>2%nat ->nat_of_Nat fd<>3%nat ->
  nat_of_Nat fd<>4%nat ->nat_of_Nat fd<>5%nat ->nat_of_Nat fd<>6%nat ->nat_of_Nat fd<>60%nat ->
  data_flags slots fd=ProcessImport.Bool_false.
Proof.
  intros ZERO ONE TWO THREE FOUR FIVE SIX SIXTY.
  unfold LeanCage_Entry_CallerWitness_FDData_flags,LeanCage_Entry_CallerWitness_FDData_lookup.
  repeat rewrite capability_nat_ite_other by
    (intro SAME;subst fd;first[
      solve[apply ZERO;reflexivity]|solve[apply ONE;reflexivity]|solve[apply TWO;reflexivity]|
      solve[apply THREE;reflexivity]|solve[apply FOUR;reflexivity]|solve[apply FIVE;reflexivity]|
      solve[apply SIX;reflexivity]|solve[apply SIXTY;reflexivity]]).
  reflexivity.
Qed.

Lemma primitive_small_bound value:
  (value<=60)%nat ->(Nat_of_nat value<=capability_descriptor_limit)%Nat.
Proof.
  intro BOUND;apply nat_le_Nat_le;apply Nat2Z.inj_le.
  rewrite nat2Natid,capability_descriptor_limit_value;lia.
Qed.

Ltac primitive_fd_cases fd:=
  destruct(Nat.eq_dec(nat_of_Nat fd)0%nat)as[FD|N0];
  [apply(f_equal Nat_of_nat)in FD;rewrite Nat2natid in FD;subst fd|
   destruct(Nat.eq_dec(nat_of_Nat fd)1%nat)as[FD|N1];
  [apply(f_equal Nat_of_nat)in FD;rewrite Nat2natid in FD;subst fd|
   destruct(Nat.eq_dec(nat_of_Nat fd)2%nat)as[FD|N2];
  [apply(f_equal Nat_of_nat)in FD;rewrite Nat2natid in FD;subst fd|
   destruct(Nat.eq_dec(nat_of_Nat fd)3%nat)as[FD|N3];
  [apply(f_equal Nat_of_nat)in FD;rewrite Nat2natid in FD;subst fd|
   destruct(Nat.eq_dec(nat_of_Nat fd)4%nat)as[FD|N4];
  [apply(f_equal Nat_of_nat)in FD;rewrite Nat2natid in FD;subst fd|
   destruct(Nat.eq_dec(nat_of_Nat fd)5%nat)as[FD|N5];
  [apply(f_equal Nat_of_nat)in FD;rewrite Nat2natid in FD;subst fd|
   destruct(Nat.eq_dec(nat_of_Nat fd)6%nat)as[FD|N6];
  [apply(f_equal Nat_of_nat)in FD;rewrite Nat2natid in FD;subst fd|
   destruct(Nat.eq_dec(nat_of_Nat fd)60%nat)as[FD|N60];
  [apply(f_equal Nat_of_nat)in FD;rewrite Nat2natid in FD;subst fd|
   idtac]]]]]]]].

Ltac primitive_retained_at old present:=
  exists(Nat_of_nat old);constructor;
    [apply primitive_small_bound;lia|exact present].
Ltac primitive_retained_known present:=first[
  solve[primitive_retained_at 0%nat present]|
  solve[primitive_retained_at 1%nat present]|
  solve[primitive_retained_at 2%nat present]|
  solve[primitive_retained_at 3%nat present]|
  solve[primitive_retained_at 4%nat present]|
  solve[primitive_retained_at 5%nat present]|
  solve[primitive_retained_at 6%nat present]|
  solve[primitive_retained_at 60%nat present]|
  solve[primitive_retained_at 7%nat present]].

Lemma primitive_retained_same slots:
  LeanCage_Entry_CallerWitness_DescriptorObjectsFrom(data_objects slots)(data_objects slots).
Proof. intros fd object BOUND PRESENT;exists fd;constructor;assumption. Qed.

Lemma primitive_snapshot_retained_0_2:
  LeanCage_Entry_CallerWitness_DescriptorObjectsFrom(data_objects(primitive_snapshot 0))(data_objects(primitive_snapshot 2)).
Proof.
  intros fd object BOUND PRESENT;primitive_fd_cases fd;
    try solve[primitive_retained_known PRESENT].
  rewrite(primitive_objects_outside _ _ N0 N1 N2 N3 N4 N5 N6 N60)in PRESENT.
  primitive_retained_known PRESENT.
Qed.

Lemma primitive_snapshot_retained_2_3:
  LeanCage_Entry_CallerWitness_DescriptorObjectsFrom(data_objects(primitive_snapshot 2))(data_objects(primitive_snapshot 3)).
Proof.
  intros fd object BOUND PRESENT;primitive_fd_cases fd;
    try solve[primitive_retained_known PRESENT].
  rewrite(primitive_objects_outside _ _ N0 N1 N2 N3 N4 N5 N6 N60)in PRESENT.
  primitive_retained_known PRESENT.
Qed.

Lemma primitive_snapshot_retained_3_4:
  LeanCage_Entry_CallerWitness_DescriptorObjectsFrom(data_objects(primitive_snapshot 3))(data_objects(primitive_snapshot 4)).
Proof.
  intros fd object BOUND PRESENT;primitive_fd_cases fd;
    try solve[primitive_retained_known PRESENT].
  rewrite(primitive_objects_outside _ _ N0 N1 N2 N3 N4 N5 N6 N60)in PRESENT.
  primitive_retained_known PRESENT.
Qed.

Lemma primitive_snapshot_retained_4_5:
  LeanCage_Entry_CallerWitness_DescriptorObjectsFrom(data_objects(primitive_snapshot 4))(data_objects(primitive_snapshot 5)).
Proof.
  intros fd object BOUND PRESENT;primitive_fd_cases fd;
    try solve[primitive_retained_known PRESENT].
  rewrite(primitive_objects_outside _ _ N0 N1 N2 N3 N4 N5 N6 N60)in PRESENT.
  primitive_retained_known PRESENT.
Qed.

Lemma primitive_snapshot_retained_5_6:
  LeanCage_Entry_CallerWitness_DescriptorObjectsFrom(data_objects(primitive_snapshot 5))(data_objects(primitive_snapshot 6)).
Proof.
  intros fd object BOUND PRESENT;primitive_fd_cases fd;
    try solve[primitive_retained_known PRESENT].
  rewrite(primitive_objects_outside _ _ N0 N1 N2 N3 N4 N5 N6 N60)in PRESENT.
  primitive_retained_known PRESENT.
Qed.

Lemma primitive_snapshot_retained_6_7:
  LeanCage_Entry_CallerWitness_DescriptorObjectsFrom(data_objects(primitive_snapshot 6))(data_objects(primitive_snapshot 7)).
Proof.
  intros fd object BOUND PRESENT;primitive_fd_cases fd;
    try solve[primitive_retained_known PRESENT].
  rewrite(primitive_objects_outside _ _ N0 N1 N2 N3 N4 N5 N6 N60)in PRESENT.
  primitive_retained_known PRESENT.
Qed.

Lemma primitive_snapshot_retained_1_0:
  LeanCage_Entry_CallerWitness_DescriptorObjectsFrom(data_objects(primitive_snapshot 1))(data_objects(primitive_snapshot 0)).
Proof.
  intros fd object BOUND PRESENT;primitive_fd_cases fd;
    try solve[primitive_retained_known PRESENT].
  rewrite(primitive_objects_outside _ _ N0 N1 N2 N3 N4 N5 N6 N60)in PRESENT.
  primitive_retained_known PRESENT.
Qed.


Record PrimitiveRetained(frame:PrimitiveFrame):Prop:={
  primitive_retained_data:LeanCage_Entry_CallerWitness_DescriptorObjectsFrom
    (data_objects(frame_before frame))(data_objects(frame_after frame))
}.
Record PrimitiveInspection(frame:PrimitiveFrame):Prop:={
  primitive_inspection_data:LeanCage_Entry_CallerWitness_DescriptorCapabilityEffect
    (data_objects(frame_before frame))(data_objects(frame_after frame))
    (data_flags(frame_before frame))(data_flags(frame_after frame))
}.

Ltac primitive_native_frame:=constructor;first[
  apply primitive_retained_same|apply primitive_snapshot_retained_0_2|apply primitive_snapshot_retained_2_3|
  apply primitive_snapshot_retained_3_4|apply primitive_snapshot_retained_4_5|
  apply primitive_snapshot_retained_5_6|apply primitive_snapshot_retained_6_7].

Definition primitive_read_frame:PrimitiveFrame:=
  LeanCage_Entry_CallerWitness_FDData_pack(Nat_of_nat 27)(Nat_of_nat 0)(Nat_of_nat 0)
    (ProcessImport.Option_some_inst1(ProcessImport.Prod_inst3 Lean.Nat(ProcessImport.List_inst1 Lean.Nat))
      (ProcessImport.Prod_mk_inst3 Lean.Nat(ProcessImport.List_inst1 Lean.Nat)(Nat_of_nat 60)
        (ProcessImport.List_cons_inst1 Lean.Nat(Nat_of_nat 165)(ProcessImport.List_nil_inst1 Lean.Nat)))).
Definition primitive_tail_codes:list nat:=
  ([7;8;9;10;11;11]++repeat 11 41++[11;12;13;14;15;16;17;18;19;20;21;11;11;11;22])%nat.
Definition primitive_tail_values:list PrimitiveFrame:=
  [primitive_read_frame;primitive_pack 4 0 2;primitive_pack 4 2 3;primitive_pack 4 3 4;
    primitive_pack 5 4 5;primitive_pack 6 5 6]++map(fun code=>primitive_pack code 6 6)primitive_tail_codes.

Lemma primitive_signal_values:
  primitive_frames LeanCage_Entry_CallerWitness_FDData_signalFrames=
    primitive_pack 0 0 0::repeat(primitive_pack 1 0 0)62++[primitive_pack 0 0 0].
Proof. reflexivity. Qed.
Lemma primitive_trace_values:
  primitive_frames LeanCage_Entry_CallerWitness_FDData_traceFrames=[primitive_pack 2 0 0;primitive_pack 3 0 0].
Proof. reflexivity. Qed.
Lemma primitive_tail_exact:
  primitive_frames LeanCage_Entry_CallerWitness_FDData_tailFrames=primitive_tail_values.
Proof. reflexivity. Qed.

Theorem primitive_signal_retained frame:
  In frame(primitive_frames LeanCage_Entry_CallerWitness_FDData_signalFrames) ->PrimitiveRetained frame.
Proof.
  rewrite primitive_signal_values;intros[FRAME|MEMBER];[subst frame;primitive_native_frame|].
  apply in_app_or in MEMBER;destruct MEMBER as[MEMBER|[FRAME|EMPTY]];try contradiction.
  - apply repeat_spec in MEMBER;subst frame;primitive_native_frame.
  - subst frame;primitive_native_frame.
Qed.
Theorem primitive_trace_retained frame:
  In frame(primitive_frames LeanCage_Entry_CallerWitness_FDData_traceFrames) ->PrimitiveRetained frame.
Proof.
  rewrite primitive_trace_values;intros[FRAME|[FRAME|EMPTY]];try contradiction;subst frame;primitive_native_frame.
Qed.
Theorem primitive_tail_retained frame:
  In frame(primitive_frames LeanCage_Entry_CallerWitness_FDData_tailFrames) ->PrimitiveRetained frame.
Proof.
  rewrite primitive_tail_exact;unfold primitive_tail_values;intro MEMBER;apply in_app_or in MEMBER.
  destruct MEMBER as[MEMBER|MEMBER].
  - cbn[In]in MEMBER;repeat destruct MEMBER as[MEMBER|MEMBER];try contradiction;subst frame;primitive_native_frame.
  - apply in_map_iff in MEMBER;destruct MEMBER as[code[SAME MEMBER]];subst frame;primitive_native_frame.
Qed.
Theorem primitive_exec_retained:PrimitiveRetained(primitive_pack 23 6 7).
Proof. primitive_native_frame. Qed.

Theorem primitive_signal_code frame:
  In frame(primitive_frames LeanCage_Entry_CallerWitness_FDData_signalFrames) ->
  (nat_of_Nat(frame_code frame)<=27)%nat.
Proof.
  rewrite primitive_signal_values;intros[FRAME|MEMBER];[subst frame;change(0<=27)%nat;lia|].
  apply in_app_or in MEMBER;destruct MEMBER as[MEMBER|[FRAME|EMPTY]];try contradiction.
  - apply repeat_spec in MEMBER;subst frame;change(1<=27)%nat;lia.
  - subst frame;change(0<=27)%nat;lia.
Qed.
Theorem primitive_trace_code frame:
  In frame(primitive_frames LeanCage_Entry_CallerWitness_FDData_traceFrames) ->
  (nat_of_Nat(frame_code frame)<=27)%nat.
Proof.
  rewrite primitive_trace_values;intros[FRAME|[FRAME|EMPTY]];try contradiction;subst frame;
    change(2<=27)%nat || change(3<=27)%nat;lia.
Qed.
Lemma primitive_tail_code_bound code:In code primitive_tail_codes ->(code<=27)%nat.
Proof.
  unfold primitive_tail_codes;intro MEMBER;repeat(apply in_app_or in MEMBER;destruct MEMBER as[MEMBER|MEMBER]).
  - cbn in MEMBER;intuition lia.
  - apply repeat_spec in MEMBER;subst code;lia.
  - cbn in MEMBER;intuition lia.
Qed.
Theorem primitive_tail_code frame:
  In frame(primitive_frames LeanCage_Entry_CallerWitness_FDData_tailFrames) ->
  (nat_of_Nat(frame_code frame)<=27)%nat.
Proof.
  rewrite primitive_tail_exact;unfold primitive_tail_values;intro MEMBER;apply in_app_or in MEMBER.
  destruct MEMBER as[MEMBER|MEMBER].
  - cbn[In]in MEMBER;repeat destruct MEMBER as[MEMBER|MEMBER];try contradiction;subst frame;
      first[change(27<=27)%nat|change(4<=27)%nat|change(5<=27)%nat|change(6<=27)%nat];lia.
  - apply in_map_iff in MEMBER;destruct MEMBER as[code[SAME MEMBER]];subst frame.
    change(nat_of_Nat(Nat_of_nat code)<=27)%nat;rewrite nat2Natid;apply primitive_tail_code_bound;exact MEMBER.
Qed.

Lemma primitive_metadata_objects:
  Lean.eq(data_objects(primitive_snapshot 1))
    (capability_open_objects(data_objects(primitive_snapshot 0))(Nat_of_nat 1)(Nat_of_nat 1000)).
Proof.
  assert(SAME:data_objects(primitive_snapshot 1)=
    capability_open_objects(data_objects(primitive_snapshot 0))(Nat_of_nat 1)(Nat_of_nat 1000)).
  { apply functional_extensionality;intro fd;primitive_fd_cases fd;try solve[vm_compute;reflexivity].
    rewrite(primitive_objects_outside _ _ N0 N1 N2 N3 N4 N5 N6 N60).
    unfold capability_open_objects;rewrite capability_nat_ite_other.
    - rewrite(primitive_objects_outside _ _ N0 N1 N2 N3 N4 N5 N6 N60);reflexivity.
    - intro SAME;subst fd;apply N1;reflexivity. }
  rewrite SAME;constructor.
Qed.

Lemma primitive_metadata_flags:
  LeanCage_Entry_CallerWitness_FlagsOutside(data_flags(primitive_snapshot 0))(data_flags(primitive_snapshot 1))(Nat_of_nat 1).
Proof.
  intros fd BOUND OTHER;primitive_fd_cases fd;try solve[vm_compute;constructor].
  - destruct(OTHER(Lean.eq_refl _)).
  - rewrite(primitive_flags_outside _ _ N0 N1 N2 N3 N4 N5 N6 N60).
    rewrite(primitive_flags_outside _ _ N0 N1 N2 N3 N4 N5 N6 N60);constructor.
Qed.

Theorem primitive_metadata_open:
  LeanCage_Entry_CallerWitness_DescriptorCapabilityEffect
    (data_objects(primitive_snapshot 0))(data_objects(primitive_snapshot 1))
    (data_flags(primitive_snapshot 0))(data_flags(primitive_snapshot 1)).
Proof.
  eapply LeanCage_Entry_CallerWitness_DescriptorCapabilityEffect_opened with(fd:=Nat_of_nat 1)(identity:=Nat_of_nat 1000).
  - apply primitive_small_bound;lia.
  - vm_compute;constructor.
  - exact primitive_metadata_objects.
  - exact primitive_metadata_flags.
Qed.

Theorem primitive_inspection_effect frame:
  In frame(primitive_frames LeanCage_Entry_CallerWitness_FDData_inspectionFrames) ->PrimitiveInspection frame.
Proof.
  change(In frame[primitive_pack 0 0 1;primitive_pack 1 1 1;primitive_pack 1 1 1;primitive_pack 2 1 0]->PrimitiveInspection frame).
  intros[FRAME|[FRAME|[FRAME|[FRAME|EMPTY]]]];try contradiction;subst frame;constructor.
  - exact primitive_metadata_open.
  - apply LeanCage_Entry_CallerWitness_DescriptorCapabilityEffect_retained,primitive_retained_same.
  - apply LeanCage_Entry_CallerWitness_DescriptorCapabilityEffect_retained,primitive_retained_same.
  - apply LeanCage_Entry_CallerWitness_DescriptorCapabilityEffect_retained,primitive_snapshot_retained_1_0.
Qed.
Theorem primitive_inspection_code frame:
  In frame(primitive_frames LeanCage_Entry_CallerWitness_FDData_inspectionFrames) ->
  nat_of_Nat(frame_code frame)=0%nat\/nat_of_Nat(frame_code frame)=1%nat\/nat_of_Nat(frame_code frame)=2%nat.
Proof.
  change(In frame[primitive_pack 0 0 1;primitive_pack 1 1 1;primitive_pack 1 1 1;primitive_pack 2 1 0]->
    nat_of_Nat(frame_code frame)=0%nat\/nat_of_Nat(frame_code frame)=1%nat\/nat_of_Nat(frame_code frame)=2%nat).
  intros[FRAME|[FRAME|[FRAME|[FRAME|EMPTY]]]];try contradiction;subst frame;cbn;auto.
Qed.

Theorem primitive_table_nonnegative slots fd binding:
  capability_descriptor_table(data_objects slots)(data_flags slots)fd=Some binding ->(0<=Int.signed fd)%Z.
Proof.
  unfold capability_descriptor_table;destruct(Z.leb 0(Int.signed fd))eqn:VALID;
    [intros;apply Z.leb_le;exact VALID|discriminate].
Qed.
Theorem primitive_snapshot_nonnegative index fd binding:
  capability_descriptor_table(data_objects(primitive_snapshot index))(data_flags(primitive_snapshot index))fd=Some binding ->
  (0<=Int.signed fd)%Z.
Proof. apply primitive_table_nonnegative. Qed.

Lemma primitive_number_other fd number:
  (0<=Int.signed fd)%Z ->Int.eq fd(Int.repr(Z.of_nat number))=false ->
  nat_of_Nat(native_descriptor_number fd)<>number.
Proof.
  intros NONNEGATIVE OTHER EQUAL;destruct(native_descriptor_number_valid fd NONNEGATIVE)as[LIMIT ROUNDTRIP].
  rewrite EQUAL in ROUNDTRIP;rewrite <-ROUNDTRIP,Int.eq_true in OTHER;discriminate.
Qed.

Ltac primitive_initial_fd_cases fd:=
  destruct(Int.eq fd(Int.repr 0))eqn:F0;
  [apply Int.same_if_eq in F0;subst fd|destruct(Int.eq fd(Int.repr 1))eqn:F1;
  [apply Int.same_if_eq in F1;subst fd|destruct(Int.eq fd(Int.repr 2))eqn:F2;
  [apply Int.same_if_eq in F2;subst fd|destruct(Int.eq fd(Int.repr 3))eqn:F3;
  [apply Int.same_if_eq in F3;subst fd|destruct(Int.eq fd(Int.repr 4))eqn:F4;
  [apply Int.same_if_eq in F4;subst fd|destruct(Int.eq fd(Int.repr 5))eqn:F5;
  [apply Int.same_if_eq in F5;subst fd|destruct(Int.eq fd(Int.repr 6))eqn:F6;
  [apply Int.same_if_eq in F6;subst fd|destruct(Int.eq fd(Int.repr 60))eqn:F60;
  [apply Int.same_if_eq in F60;subst fd|idtac]]]]]]]].

Theorem primitive_initial_table:
  capability_descriptor_table(data_objects(primitive_snapshot 0))(data_flags(primitive_snapshot 0))=fork_fixture_worker_table.
Proof.
  apply functional_extensionality;intro fd;primitive_initial_fd_cases fd;tryif is_var fd then idtac else solve[vm_compute;reflexivity].
  change(Int.eq fd Int.zero=false)in F0.
  rewrite namespace_useful_worker_table_exact;unfold fork_fixture_worker_slot;rewrite F0,F2,F4,F5,F6,F60.
  unfold capability_descriptor_table;destruct(Z.leb 0(Int.signed fd))eqn:VALID;[|reflexivity].
  apply Z.leb_le in VALID.
  assert(N0:nat_of_Nat(native_descriptor_number fd)<>0%nat)by(eapply primitive_number_other;[exact VALID|exact F0]).
  assert(N1:nat_of_Nat(native_descriptor_number fd)<>1%nat)by(eapply primitive_number_other;[exact VALID|exact F1]).
  assert(N2:nat_of_Nat(native_descriptor_number fd)<>2%nat)by(eapply primitive_number_other;[exact VALID|exact F2]).
  assert(N3:nat_of_Nat(native_descriptor_number fd)<>3%nat)by(eapply primitive_number_other;[exact VALID|exact F3]).
  assert(N4:nat_of_Nat(native_descriptor_number fd)<>4%nat)by(eapply primitive_number_other;[exact VALID|exact F4]).
  assert(N5:nat_of_Nat(native_descriptor_number fd)<>5%nat)by(eapply primitive_number_other;[exact VALID|exact F5]).
  assert(N6:nat_of_Nat(native_descriptor_number fd)<>6%nat)by(eapply primitive_number_other;[exact VALID|exact F6]).
  assert(N60:nat_of_Nat(native_descriptor_number fd)<>60%nat)by(eapply primitive_number_other;[exact VALID|exact F60]).
  rewrite(primitive_objects_outside _ _ N0 N1 N2 N3 N4 N5 N6 N60);reflexivity.
Qed.
