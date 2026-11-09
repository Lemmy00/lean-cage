(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.origin: Decode genuine descriptor effects at the same recorded primitive. *)
From Stdlib Require Import ZArith List Lia Bool Classical_Prop FunctionalExtensionality.
From compcert Require Import Integers Values.
From LeanImport Require Import Lean.
From EntryProcess Require Import ProcessImport ProcessCapabilityRecording ProcessCgroupRecording.
From EntryNamespace Require Import NamespaceObjects NamespaceHandles NamespacePhysical NamespaceCapabilities.
Import ListNotations.
Local Close Scope lean_scope.
Local Open Scope Z_scope.

Fixpoint capability_binary_maximum(bits:nat):Lean.Nat:=match bits with
  |O=>Nat_zero|S remaining=>Nat_succ(double(capability_binary_maximum remaining))end.
Definition capability_descriptor_limit:=capability_binary_maximum 31.


Lemma capability_descriptor_limit_value:
  Z.of_nat(nat_of_Nat capability_descriptor_limit)=2147483647.
Proof.
  unfold capability_descriptor_limit;cbn[capability_binary_maximum].
  repeat first[rewrite physical_double_exact|rewrite physical_succ_exact].
  repeat first[rewrite Nat2Z.inj_add|rewrite Nat2Z.inj_mul|rewrite Nat2Z.inj_succ].
  cbn[nat_of_Nat];reflexivity.
Qed.

Lemma capability_descriptor_bound code:
  (code<=capability_descriptor_limit)%Nat ->(Z.of_nat(nat_of_Nat code)<=2147483647)%Z.
Proof. intro BOUND;eapply recorded_imported_descriptor_bound;[exact capability_descriptor_limit_value|exact BOUND]. Qed.

Lemma capability_native_bound fd:
  (0<=Int.signed fd)%Z ->(native_descriptor_number fd<=capability_descriptor_limit)%Nat.
Proof.
  intro NONNEGATIVE;apply nat_le_Nat_le;apply Nat2Z.inj_le.
  rewrite capability_descriptor_limit_value.
  destruct(native_descriptor_number_valid fd NONNEGATIVE)as[BOUND NUMBER].
  apply Z.leb_le in BOUND;change(Z.of_nat(nat_of_Nat(native_descriptor_number fd))<=2147483647)%Z in BOUND.
  exact BOUND.
Qed.

Definition capability_descriptor_table
    (objects:Lean.Nat->ProcessImport.Option_inst1 Lean.Nat)(flags:Lean.Nat->ProcessImport.Bool):DescriptorTable:=
  fun fd=>if Z.leb 0(Int.signed fd)then
    match objects(native_descriptor_number fd)with
    |ProcessImport.Option_none_inst1 _=>None
    |ProcessImport.Option_some_inst1 _ object=>Some
      {|descriptor_object:=physical_object(nat_of_Nat object);
        descriptor_cloexec:=physical_bool(flags(native_descriptor_number fd))|}
    end else None.

Lemma capability_tick_table tick actor:
  physical_tick_table tick actor=capability_descriptor_table
    (ProcessImport.objects tick(Nat_of_nat actor))(ProcessImport.cloexec tick(Nat_of_nat actor)).
Proof. reflexivity. Qed.

Lemma capability_strict_previous before after fd object:
  LeanCage_Entry_CallerWitness_DescriptorObjectsFrom before after ->
  (fd<=capability_descriptor_limit)%Nat ->after fd=ProcessImport.Option_some_inst1 Lean.Nat object ->
  exists old,(Z.of_nat(nat_of_Nat old)<=2147483647)%Z /\
    before old=ProcessImport.Option_some_inst1 Lean.Nat object.
Proof.
  intros FRAME BOUND PRESENT;apply NNPP;intro NONE.
  cut Lean.sEmpty;[destruct 1|].
  assert(ACTUAL:Lean.eq(after fd)(ProcessImport.Option_some_inst1 Lean.Nat object))by(rewrite PRESENT;constructor).
  destruct(FRAME fd object BOUND ACTUAL)as[old[OLD PRIOR]].
  exfalso;apply NONE;exists old;split;[apply capability_descriptor_bound;exact OLD|destruct PRIOR;reflexivity].
Qed.

Theorem capability_objects_from before after before_flags after_flags:
  LeanCage_Entry_CallerWitness_DescriptorObjectsFrom before after ->
  table_objects_from(capability_descriptor_table before before_flags)(capability_descriptor_table after after_flags).
Proof.
  intros FRAME fd binding PRESENT;unfold capability_descriptor_table in PRESENT.
  destruct(Z.leb 0(Int.signed fd))eqn:NONNEGATIVE;[|discriminate].
  apply Z.leb_le in NONNEGATIVE.
  destruct(after(native_descriptor_number fd))as[|object]eqn:AFTER;[discriminate|].
  inversion PRESENT;subst binding.
  destruct(capability_strict_previous _ _ _ _ FRAME(capability_native_bound fd NONNEGATIVE)AFTER)
    as[old[BOUND PRIOR]].
  destruct(recorded_nat_descriptor old BOUND)as[VALID NUMBER].
  exists(Int.repr(Z.of_nat(nat_of_Nat old))),
    {|descriptor_object:=physical_object(nat_of_Nat object);descriptor_cloexec:=physical_bool(before_flags old)|}.
  split;[|reflexivity].
  assert(VALID_TEST:Z.leb 0(Int.signed(Int.repr(Z.of_nat(nat_of_Nat old))))=true)
    by(apply Z.leb_le;exact VALID).
  unfold capability_descriptor_table;rewrite VALID_TEST,NUMBER,PRIOR;reflexivity.
Qed.

Lemma capability_nat_ite_same(A:Type)first second(yes no:A):
  first=second ->
  ProcessImport.ite A(Lean.eq first second)(ProcessImport.instDecidableEqNat first second)yes no=yes.
Proof.
  intro SAME;subst second;unfold ProcessImport.ite,ProcessImport.dite.
  destruct(ProcessImport.instDecidableEqNat first first)as[decision REFLECT].
  destruct decision;cbn in *;[|reflexivity].
  cut Lean.sEmpty;[destruct 1|];destruct(REFLECT(Lean.eq_refl first)).
Qed.

Lemma capability_nat_ite_other(A:Type)first second(yes no:A):
  first<>second ->
  ProcessImport.ite A(Lean.eq first second)(ProcessImport.instDecidableEqNat first second)yes no=no.
Proof.
  intro DIFFERENT;unfold ProcessImport.ite,ProcessImport.dite.
  destruct(ProcessImport.instDecidableEqNat first second)as[decision REFLECT].
  destruct decision;cbn in *;[reflexivity|].
  cut Lean.sEmpty;[destruct 1|];destruct REFLECT;exfalso;apply DIFFERENT;reflexivity.
Qed.

Lemma capability_ordinary_code identity:
  physical_object(nat_of_Nat
    (ProcessImport.Nat_mul(Nat_succ(double(Nat_succ(double Nat_zero))))identity))=
    ordinary_object(nat_of_Nat identity).
Proof.
  rewrite physical_mul_exact;cbn[nat_of_Nat double].
  replace(3*nat_of_Nat identity)%nat with(descriptor_object_code(ordinary_object(nat_of_Nat identity)))
    by(unfold descriptor_object_code;lia).
  apply physical_object_code_exact.
Qed.

Definition capability_open_objects before(fd identity:Lean.Nat):=
  fun query=>ProcessImport.ite(ProcessImport.Option_inst1 Lean.Nat)(Lean.eq query fd)
    (ProcessImport.instDecidableEqNat query fd)
    (ProcessImport.Option_some_inst1 Lean.Nat
      (ProcessImport.Nat_mul(Nat_succ(double(Nat_succ(double Nat_zero))))identity))(before query).

Lemma capability_open_flags before_flags after_flags fd query:
  LeanCage_Entry_CallerWitness_FlagsOutside before_flags after_flags fd ->
  (query<=capability_descriptor_limit)%Nat ->query<>fd ->after_flags query=before_flags query.
Proof.
  intros FLAGS BOUND OTHER.
  assert(DIFFERENT:ProcessImport.Ne Lean.Nat query fd).
  { intro SAME;destruct SAME;exfalso;apply OTHER;reflexivity. }
  pose proof(FLAGS query BOUND DIFFERENT)as SAME;destruct SAME;reflexivity.
Qed.

Lemma capability_open_table before after before_flags after_flags fd identity:
  (fd<=capability_descriptor_limit)%Nat ->
  Lean.eq after(capability_open_objects before fd identity) ->
  LeanCage_Entry_CallerWitness_FlagsOutside before_flags after_flags fd ->
  capability_descriptor_table after after_flags=
    table_put(capability_descriptor_table before before_flags)(Int.repr(Z.of_nat(nat_of_Nat fd)))
      {|descriptor_object:=ordinary_object(nat_of_Nat identity);
        descriptor_cloexec:=physical_bool(after_flags fd)|}.
Proof.
  intros BOUND TABLE FLAGS.
  assert(TABLE_VALUE:after=capability_open_objects before fd identity)by(destruct TABLE;reflexivity).
  rewrite TABLE_VALUE.
  destruct(recorded_nat_descriptor fd(capability_descriptor_bound fd BOUND))as[NONNEGATIVE NUMBER].
  apply functional_extensionality;intro query;unfold table_put.
  destruct(Int.eq query(Int.repr(Z.of_nat(nat_of_Nat fd))))eqn:SAME.
  - apply Int.same_if_eq in SAME;subst query.
    assert(VALID:Z.leb 0(Int.signed(Int.repr(Z.of_nat(nat_of_Nat fd))))=true)
      by(apply Z.leb_le;exact NONNEGATIVE).
    unfold capability_descriptor_table;rewrite VALID.
    rewrite NUMBER;unfold capability_open_objects;rewrite capability_nat_ite_same by reflexivity.
    rewrite capability_ordinary_code;reflexivity.
  - unfold capability_descriptor_table.
    destruct(Z.leb 0(Int.signed query))eqn:VALID.
    + apply Z.leb_le in VALID.
      assert(OTHER:native_descriptor_number query<>fd).
      { intro EQUAL;destruct(native_descriptor_number_valid query VALID)as[LIMIT ROUNDTRIP].
        rewrite EQUAL in ROUNDTRIP;subst query;rewrite Int.eq_true in SAME;discriminate. }
      unfold capability_open_objects;rewrite capability_nat_ite_other by exact OTHER.
      rewrite(capability_open_flags _ _ _ _ FLAGS(capability_native_bound query VALID)OTHER);reflexivity.
    + reflexivity.
Qed.

Theorem recorded_descriptor_open_step before_world actor before after before_flags after_flags fd identity can_acquire:
  capability_tables before_world actor=capability_descriptor_table before before_flags ->
  (fd<=capability_descriptor_limit)%Nat ->
  Lean.eq(before fd)(ProcessImport.Option_none_inst1 Lean.Nat) ->
  Lean.eq after(capability_open_objects before fd identity) ->
  LeanCage_Entry_CallerWitness_FlagsOutside before_flags after_flags fd ->
  capability_step can_acquire before_world(capability_open actor)
    (capability_retable before_world actor(capability_descriptor_table after after_flags)).
Proof.
  intros BEFORE BOUND FRESH TABLE FLAGS.
  rewrite(capability_open_table _ _ _ _ _ _ BOUND TABLE FLAGS),<-BEFORE.
  apply capability_open_step.
  destruct(recorded_nat_descriptor fd(capability_descriptor_bound fd BOUND))as[NONNEGATIVE NUMBER].
  rewrite BEFORE;unfold capability_descriptor_table.
  assert(VALID:Z.leb 0(Int.signed(Int.repr(Z.of_nat(nat_of_Nat fd))))=true)
    by(apply Z.leb_le;exact NONNEGATIVE).
  assert(FRESH_VALUE:before fd=ProcessImport.Option_none_inst1 Lean.Nat)by(destruct FRESH;reflexivity).
  rewrite VALID,NUMBER,FRESH_VALUE;reflexivity.
Qed.

Lemma capability_pending_identity world:capability_pending world(capability_messages world)=world.
Proof. destruct world;reflexivity. Qed.

Lemma recorded_capability_step_effect can_acquire before action after:
  capability_step can_acquire before action after ->CapabilityEffect can_acquire before action after.
Proof.
  intro STEP;rewrite <-(capability_pending_identity after).
  econstructor;[exact STEP|apply incl_refl].
Qed.

Theorem capability_descriptor_effect_step before_world actor before after before_flags after_flags can_acquire:
  capability_tables before_world actor=capability_descriptor_table before before_flags ->
  LeanCage_Entry_CallerWitness_DescriptorCapabilityEffect before after before_flags after_flags ->
  exists action,(action=capability_local actor\/action=capability_open actor) /\
    capability_step can_acquire before_world action
      (capability_retable before_world actor(capability_descriptor_table after after_flags)).
Proof.
  intros BEFORE EFFECT;apply NNPP;intro NONE;cut Lean.sEmpty;[destruct 1|].
  destruct EFFECT as[FRAME|fd identity BOUND FRESH TABLE FLAGS];exfalso;apply NONE.
  - exists(capability_local actor);split;[left;reflexivity|].
    apply capability_local_step;rewrite BEFORE;apply capability_objects_from;exact FRAME.
  - exists(capability_open actor);split;[right;reflexivity|].
    eapply recorded_descriptor_open_step;[exact BEFORE|exact BOUND|exact FRESH|exact TABLE|exact FLAGS].
Qed.

Definition PrimitiveDescriptorObservation:=nat->nat->ProcessImport.Bool->LeanCage_Entry_CallerPhysical_Tick->
  (Lean.Nat->ProcessImport.Option_inst1 Lean.Nat)->(Lean.Nat->ProcessImport.Bool)->
  (Lean.Nat->ProcessImport.Option_inst1 Lean.Nat)->(Lean.Nat->ProcessImport.Bool)->Prop.

(* The observation parameter denotes the actual indexed returned primitive.
   The sample retains that position, the actual maps, and its opcode/origin
   label. This is not an independently chosen opcode or descriptor frame. *)
Record PrimitiveDescriptorSample(observation:PrimitiveDescriptorObservation)
    (ticks:list LeanCage_Entry_CallerPhysical_Tick)(family:LeanCage_Entry_CallerPhysical_PrimitiveFamily)
    (actor code:nat)(origin:ProcessImport.Bool)(before:CapabilityWorld)(tick:LeanCage_Entry_CallerPhysical_Tick)
    (after:CapabilityWorld):Type:={
  descriptor_position:nat;
  descriptor_before_objects:Lean.Nat->ProcessImport.Option_inst1 Lean.Nat;
  descriptor_before_flags:Lean.Nat->ProcessImport.Bool;
  descriptor_after_objects:Lean.Nat->ProcessImport.Option_inst1 Lean.Nat;
  descriptor_after_flags:Lean.Nat->ProcessImport.Bool;
  descriptor_actual:observation descriptor_position code origin tick descriptor_before_objects descriptor_before_flags
    descriptor_after_objects descriptor_after_flags;
  descriptor_selected:nth_error ticks descriptor_position=Some tick;
  descriptor_label:LeanCage_Entry_CallerPhysical_Tick_primitive tick=
    ProcessImport.Option_some_inst1 LeanCage_Entry_CallerPhysical_PrimitiveLabel
      (LeanCage_Entry_CallerPhysical_PrimitiveLabel_mk family(Nat_of_nat code)origin);
  descriptor_observed:CapabilityObserved tick before;
  descriptor_objects:ProcessImport.objects tick(Nat_of_nat actor)=descriptor_before_objects;
  descriptor_flags:ProcessImport.cloexec tick(Nat_of_nat actor)=descriptor_before_flags;
  descriptor_after_table:capability_tables after actor=
    capability_descriptor_table descriptor_after_objects descriptor_after_flags
}.
Arguments descriptor_position {observation ticks family actor code origin before tick after} _.
Arguments descriptor_before_objects {observation ticks family actor code origin before tick after} _.
Arguments descriptor_before_flags {observation ticks family actor code origin before tick after} _.
Arguments descriptor_after_objects {observation ticks family actor code origin before tick after} _.
Arguments descriptor_after_flags {observation ticks family actor code origin before tick after} _.
Arguments descriptor_actual {observation ticks family actor code origin before tick after} _.
Arguments descriptor_selected {observation ticks family actor code origin before tick after} _.
Arguments descriptor_label {observation ticks family actor code origin before tick after} _.
Arguments descriptor_observed {observation ticks family actor code origin before tick after} _.
Arguments descriptor_objects {observation ticks family actor code origin before tick after} _.
Arguments descriptor_flags {observation ticks family actor code origin before tick after} _.
Arguments descriptor_after_table {observation ticks family actor code origin before tick after} _.

Lemma descriptor_sample_before_table observation ticks family actor code origin before tick after
    (sample:PrimitiveDescriptorSample observation ticks family actor code origin before tick after):
  capability_tables before actor=capability_descriptor_table(descriptor_before_objects sample)(descriptor_before_flags sample).
Proof.
  apply functional_extensionality;intro fd;rewrite(descriptor_observed sample).
  unfold physical_tick_table,capability_descriptor_table;rewrite(descriptor_objects sample),(descriptor_flags sample);reflexivity.
Qed.

Definition descriptor_child_key child:=nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey child).

Inductive RecordedNativeCapability(observation:PrimitiveDescriptorObservation)
    (ticks:list LeanCage_Entry_CallerPhysical_Tick)can_acquire(owner child:LeanCage_Entry_ProcessIdentity):
    nat->ProcessImport.Bool->CapabilityWorld->LeanCage_Entry_CallerPhysical_Tick->CapabilityAction->CapabilityWorld->Prop:=
| recorded_native_retained:forall code origin before tick after
    (sample:PrimitiveDescriptorSample observation ticks LeanCage_Entry_CallerPhysical_PrimitiveFamily_native
      (descriptor_child_key child)code origin before tick after),
    LeanCage_Entry_CallerWitness_DescriptorObjectsFrom(descriptor_before_objects sample)(descriptor_after_objects sample) ->
    after=capability_retable before(descriptor_child_key child)
      (capability_descriptor_table(descriptor_after_objects sample)(descriptor_after_flags sample)) ->
    RecordedNativeCapability observation ticks can_acquire owner child code origin before tick
      (capability_local(descriptor_child_key child))after
| recorded_native_untrusted:forall code origin before tick after action
    (sample:PrimitiveDescriptorSample observation ticks LeanCage_Entry_CallerPhysical_PrimitiveFamily_native
      (descriptor_child_key child)code origin before tick after),
    (LeanCage_Entry_CallerPhysical_ContextSafe owner(LeanCage_Entry_CallerPhysical_Tick_before tick) ->
      origin=ProcessImport.Bool_true ->LeanCage_Entry_CallerPhysical_LocalEntryCode(Nat_of_nat code) ->Lean.sEmpty) ->
    CapabilityEffect can_acquire before action after ->
    RecordedNativeCapability observation ticks can_acquire owner child code origin before tick action after.

Theorem recorded_native_capability_contract observation ticks can_acquire owner child:
  NativeCapabilityContract(RecordedNativeCapability observation ticks can_acquire owner child)can_acquire owner child.
Proof.
  constructor.
  - intros code origin before tick action after OP;destruct OP as[code origin before tick after sample FRAME AFTER|
      code origin before tick after action sample REJECT EFFECT];[|exact EFFECT].
    rewrite AFTER;apply recorded_capability_step_effect,capability_local_step.
    rewrite(descriptor_sample_before_table _ _ _ _ _ _ _ _ _ sample).
    apply capability_objects_from;exact FRAME.
  - intros code origin before tick action after OP SAFE GENUINE CODE;destruct OP;[reflexivity|].
    cut Lean.sEmpty;[destruct 1|];eapply H;[exact SAFE|exact GENUINE|exact CODE].
Qed.

Inductive RecordedMetadataCapability(observation:PrimitiveDescriptorObservation)
    (ticks:list LeanCage_Entry_CallerPhysical_Tick)can_acquire(owner child:LeanCage_Entry_ProcessIdentity):
    nat->ProcessImport.Bool->CapabilityWorld->LeanCage_Entry_CallerPhysical_Tick->CapabilityAction->CapabilityWorld->Prop:=
| recorded_metadata_genuine:forall code origin before tick after action
    (sample:PrimitiveDescriptorSample observation ticks LeanCage_Entry_CallerPhysical_PrimitiveFamily_metadata
      (descriptor_child_key child)code origin before tick after),
    LeanCage_Entry_CallerWitness_DescriptorCapabilityEffect(descriptor_before_objects sample)(descriptor_after_objects sample)
      (descriptor_before_flags sample)(descriptor_after_flags sample) ->
    after=capability_retable before(descriptor_child_key child)
      (capability_descriptor_table(descriptor_after_objects sample)(descriptor_after_flags sample)) ->
    (action=capability_local(descriptor_child_key child)\/action=capability_open(descriptor_child_key child)) ->
    capability_step can_acquire before action after ->
    RecordedMetadataCapability observation ticks can_acquire owner child code origin before tick action after
| recorded_metadata_untrusted:forall code origin before tick after action
    (sample:PrimitiveDescriptorSample observation ticks LeanCage_Entry_CallerPhysical_PrimitiveFamily_metadata
      (descriptor_child_key child)code origin before tick after),
    (LeanCage_Entry_CallerPhysical_ContextSafe owner(LeanCage_Entry_CallerPhysical_Tick_before tick) ->
      origin=ProcessImport.Bool_true ->(code=0%nat\/code=1%nat\/code=2%nat) ->Lean.sEmpty) ->
    CapabilityEffect can_acquire before action after ->
    RecordedMetadataCapability observation ticks can_acquire owner child code origin before tick action after.

Theorem recorded_metadata_capability_contract observation ticks can_acquire owner child:
  MetadataCapabilityContract(RecordedMetadataCapability observation ticks can_acquire owner child)can_acquire owner child.
Proof.
  constructor.
  - intros code origin before tick action after OP;destruct OP;[apply recorded_capability_step_effect;exact H2|exact H0].
  - intros code origin before tick action after OP SAFE GENUINE CODE;destruct OP;[exact H1|].
    cut Lean.sEmpty;[destruct 1|];eapply H;[exact SAFE|exact GENUINE|exact CODE].
Qed.

Theorem recorded_metadata_capability_from_sample observation ticks can_acquire owner child code origin before tick after
    (sample:PrimitiveDescriptorSample observation ticks LeanCage_Entry_CallerPhysical_PrimitiveFamily_metadata
      (descriptor_child_key child)code origin before tick after):
  LeanCage_Entry_CallerWitness_DescriptorCapabilityEffect(descriptor_before_objects sample)(descriptor_after_objects sample)
    (descriptor_before_flags sample)(descriptor_after_flags sample) ->
  after=capability_retable before(descriptor_child_key child)
    (capability_descriptor_table(descriptor_after_objects sample)(descriptor_after_flags sample)) ->
  exists action,RecordedMetadataCapability observation ticks can_acquire owner child code origin before tick action after.
Proof.
  intros EFFECT AFTER.
  destruct(capability_descriptor_effect_step before(descriptor_child_key child)_ _ _ _ can_acquire
    (descriptor_sample_before_table _ _ _ _ _ _ _ _ _ sample)EFFECT)as[action[PROFILE STEP]].
  exists action;eapply recorded_metadata_genuine with(sample:=sample);try eassumption.
  rewrite AFTER;exact STEP.
Qed.
