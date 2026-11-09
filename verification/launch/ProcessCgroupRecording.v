(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.origin: Connect actual cgroup objects and descriptor tables to ordinary Lean. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers Values.
From LeanImport Require Import Lean.
From EntryProcess Require Import ProcessImport ProcessScope ProcessScopeRecording ProcessCallerConnection.
From EntryNamespace Require Import NamespaceObjects NamespaceHandles NamespacePhysical.
Import ListNotations.
Local Close Scope lean_scope.

Definition recorded_cgroup_objects(groups:nat->option nat)(code:Lean.Nat):
    ProcessImport.Option_inst1 Lean.Nat :=
  match physical_object(nat_of_Nat code)with
  |ordinary_object object=>match groups object with
    |None=>ProcessImport.Option_none_inst1 Lean.Nat
    |Some group=>ProcessImport.Option_some_inst1 Lean.Nat(Nat_of_nat group)end
  |release_endpoint _ _=>ProcessImport.Option_none_inst1 Lean.Nat end.

Lemma recorded_cgroup_object groups object:
  recorded_cgroup_objects groups(native_descriptor_object object)=
    match object with
    |ordinary_object identity=>match groups identity with
      |None=>ProcessImport.Option_none_inst1 Lean.Nat
      |Some group=>ProcessImport.Option_some_inst1 Lean.Nat(Nat_of_nat group)end
    |release_endpoint _ _=>ProcessImport.Option_none_inst1 Lean.Nat end.
Proof.
  unfold recorded_cgroup_objects;rewrite native_descriptor_object_exact,physical_object_code_exact;reflexivity.
Qed.

Lemma recorded_nat_descriptor fd:
  (Z.of_nat(nat_of_Nat fd)<=2147483647)%Z ->
  (0<=Int.signed(Int.repr(Z.of_nat(nat_of_Nat fd))))%Z /\
  native_descriptor_number(Int.repr(Z.of_nat(nat_of_Nat fd)))=fd.
Proof.
  intro BOUND;assert(RANGE:(0<=Z.of_nat(nat_of_Nat fd)<=Int.max_signed)%Z).
  { change(0<=Z.of_nat(nat_of_Nat fd)<=2147483647)%Z;lia. }
  change Int.max_signed with 2147483647 in RANGE.
  split.
  - rewrite Int.signed_repr;[lia|].
    change(-2147483648<=Z.of_nat(nat_of_Nat fd)<=2147483647)%Z;lia.
  - unfold native_descriptor_number;rewrite Int.unsigned_repr.
    + rewrite Nat2Z.id;apply Nat2natid.
    + change(0<=Z.of_nat(nat_of_Nat fd)<=4294967295)%Z;lia.
Qed.

Lemma recorded_imported_descriptor_bound fd limit:
  Z.of_nat(nat_of_Nat limit)=2147483647%Z ->(fd<=limit)%Nat ->
  (Z.of_nat(nat_of_Nat fd)<=2147483647)%Z.
Proof.
  intros LIMIT BOUND;pose proof(Nat_le_nat_le' _ _ BOUND)as BOUNDED.
  apply Nat2Z.inj_le in BOUNDED.
  rewrite LIMIT in BOUNDED;exact BOUNDED.
Qed.

Lemma recorded_tick_object tick actor fd code:
  (Z.of_nat(nat_of_Nat fd)<=2147483647)%Z ->
  ProcessImport.objects tick(LeanCage_Entry_CallerPhysical_taskKey actor)fd=
    ProcessImport.Option_some_inst1 Lean.Nat code ->
  exists flag,physical_tick_table tick
    (nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor))
    (Int.repr(Z.of_nat(nat_of_Nat fd)))=
      Some{|descriptor_object:=physical_object(nat_of_Nat code);descriptor_cloexec:=flag|}.
Proof.
  intros BOUND PRESENT;destruct(recorded_nat_descriptor fd BOUND)as[NONNEGATIVE NUMBER].
  assert(VALID:Z.leb 0(Int.signed(Int.repr(Z.of_nat(nat_of_Nat fd))))=true)
    by(apply Z.leb_le;exact NONNEGATIVE).
  unfold physical_tick_table;rewrite VALID,Nat2natid,NUMBER,PRESENT.
  eexists;reflexivity.
Qed.

Theorem actual_cgroup_absence_produces_ordinary groups tick actor:
  (forall object group,groups object=Some group ->
    object_absent(physical_tick_table tick
      (nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor)))(ordinary_object object)) ->
  LeanCage_Entry_CallerPhysical_CgroupAbsent(recorded_cgroup_objects groups)tick actor.
Proof.
  intros ABSENT fd code BOUND PRESENT.
  assert(BOUNDED:(Z.of_nat(nat_of_Nat fd)<=2147483647)%Z).
  { eapply recorded_imported_descriptor_bound;[|exact BOUND].
    rewrite physical_ofnat_exact.
    repeat first[rewrite physical_double_exact|rewrite physical_succ_exact].
    repeat first[rewrite Nat2Z.inj_add|rewrite Nat2Z.inj_mul|rewrite Nat2Z.inj_succ].
    cbn[nat_of_Nat];vm_compute;reflexivity. }
  assert(LOOKUP:ProcessImport.objects tick(LeanCage_Entry_CallerPhysical_taskKey actor)fd=
      ProcessImport.Option_some_inst1 Lean.Nat code)by(destruct PRESENT;reflexivity).
  destruct(recorded_tick_object _ _ _ _ BOUNDED LOOKUP)as[flag BINDING].
  unfold recorded_cgroup_objects;destruct(physical_object(nat_of_Nat code))as[object|channel side]eqn:OBJECT;
    [|constructor].
  destruct(groups object)as[group|]eqn:GROUP;[|constructor].
  exfalso;eapply(ABSENT _ _ GROUP);[exact BINDING|reflexivity].
Qed.

Theorem actual_placement_produces_ordinary groups tick:
  PlacementRecording groups tick ->
  LeanCage_Entry_CallerPhysical_PlacementRecording(recorded_cgroup_objects groups)tick.
Proof.
  intros RECORDED group PLACED.
  assert(ACTION:LeanCage_Entry_CallerPhysical_Tick_action tick=
    LeanCage_Entry_CallerPhysical_Action_placement group)by(destruct PLACED;reflexivity).
  destruct(RECORDED group ACTION)as[actor[fd[binding[object[bytes[lost[SOCKET[PRESENT[OBJECT GROUP]]]]]]]]].
  assert(NONNEGATIVE:(0<=Int.signed fd)%Z).
  { unfold physical_tick_table in PRESENT;destruct(Z.leb 0(Int.signed fd))eqn:VALID;
      [apply Z.leb_le;exact VALID|discriminate]. }
  unfold physical_tick_table in PRESENT.
  assert(VALID:Z.leb 0(Int.signed fd)=true)by(apply Z.leb_le;exact NONNEGATIVE).
  rewrite VALID in PRESENT.
  destruct(ProcessImport.objects tick(Nat_of_nat(nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor)))
    (native_descriptor_number fd))as[|code]eqn:LOOKUP;[discriminate|].
  inversion PRESENT;subst binding;cbn[descriptor_object]in OBJECT.
  rewrite Nat2natid in LOOKUP.
  exists actor,(native_descriptor_number fd),code,bytes,lost.
  constructor.
  - apply nat_le_Nat_le;apply Nat2Z.inj_le;rewrite physical_ofnat_exact.
    repeat first[rewrite physical_double_exact|rewrite physical_succ_exact].
    repeat first[rewrite Nat2Z.inj_add|rewrite Nat2Z.inj_mul|rewrite Nat2Z.inj_succ].
    cbn[nat_of_Nat].
    unfold native_descriptor_number;rewrite nat2Natid.
    pose proof(Int.unsigned_range fd)as RANGE.
    assert(LIMIT:(Int.unsigned fd<=Int.max_signed)%Z)by(apply Int.signed_positive;lia).
    change(Int.unsigned fd<=2147483647)%Z in LIMIT;lia.
  - constructor.
    + change(Lean.eq(ProcessImport.socket tick)
        (LeanCage_Entry_CallerPhysical_SocketObservation_wrote actor(native_descriptor_number fd)bytes lost)).
      rewrite SOCKET;constructor.
    + constructor.
      * change(Lean.eq(ProcessImport.objects tick(LeanCage_Entry_CallerPhysical_taskKey actor)
          (native_descriptor_number fd))(ProcessImport.Option_some_inst1 Lean.Nat code)).
        rewrite LOOKUP;constructor.
      * unfold recorded_cgroup_objects;rewrite OBJECT,GROUP,Nat2natid;constructor.
Qed.

Theorem actual_writer_absence_produces_ordinary groups tick:
  (forall actor fd bytes lost,ProcessImport.socket tick=
    LeanCage_Entry_CallerPhysical_SocketObservation_wrote actor fd bytes lost ->
    forall object group,groups object=Some group ->
      object_absent(physical_tick_table tick
        (nat_of_Nat(LeanCage_Entry_CallerPhysical_taskKey actor)))(ordinary_object object)) ->
  LeanCage_Entry_CallerPhysical_WriteOutsideCgroup(recorded_cgroup_objects groups)tick.
Proof.
  intros ABSENT actor fd bytes lost object BOUND WROTE PRESENT.
  assert(SOCKET:ProcessImport.socket tick=
    LeanCage_Entry_CallerPhysical_SocketObservation_wrote actor fd bytes lost)by(destruct WROTE;reflexivity).
  exact(actual_cgroup_absence_produces_ordinary groups tick actor(ABSENT _ _ _ _ SOCKET)
    fd object BOUND PRESENT).
Qed.
