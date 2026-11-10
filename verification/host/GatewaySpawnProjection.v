(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: The same native descriptor observations produce the imported engine view. *)
From Stdlib Require Import ZArith List Lia.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewaySpawnImport GatewaySpawnDescriptors GatewaySpawnResources.
Local Close Scope lean_scope.
Open Scope Z_scope.

Definition gateway_shared_descriptor (entry : gateway_resource_descriptor) :=
  LeanCage_Host_NativeSpawn_Descriptor_mk
    (Nat_of_nat (gateway_resource_object (gateway_descriptor_object entry)))
    (Nat_of_nat (gateway_resource_description (gateway_descriptor_object entry)))
    (if gateway_descriptor_cloexec entry then Bool_true else Bool_false).

Definition gateway_shared_descriptors (table : gateway_descriptor_table gateway_open_description) (fd : Lean.Nat) :=
  match table (Z.of_nat (nat_of_Nat fd)) with
  | None => Option_none_inst1 LeanCage_Host_NativeSpawn_Descriptor
  | Some entry => Option_some_inst1 LeanCage_Host_NativeSpawn_Descriptor (gateway_shared_descriptor entry)
  end.

Lemma gateway_shared_nat_separate first second :
  first <> second -> Ne Lean.Nat (Nat_of_nat first) (Nat_of_nat second).
Proof.
  revert second; induction first as [| first IH]; intros [|second] DIFFERENT;
    unfold Ne, Not; cbn [Nat_of_nat].
  - exfalso; apply DIFFERENT; reflexivity.
  - intro EQUAL; inversion EQUAL.
  - intro EQUAL; inversion EQUAL.
  - intro EQUAL; apply (IH second ltac:(lia)).
    inversion EQUAL; reflexivity.
Qed.

Theorem gateway_shared_channel_evidence table data control :
  table 0 = Some data -> table 1 = Some data -> table 3 = Some control ->
  gateway_descriptor_cloexec data = false -> gateway_descriptor_cloexec control = false ->
  gateway_resource_object (gateway_descriptor_object data) <>
    gateway_resource_object (gateway_descriptor_object control) ->
  LeanCage_Host_NativeSpawn_ChannelEvidence (gateway_shared_descriptors table)
    (gateway_shared_descriptor data) (gateway_shared_descriptor control).
Proof.
  intros INPUT OUTPUT CANCELLATION DATA_FLAGS CONTROL_FLAGS SEPARATE.
  unfold LeanCage_Host_NativeSpawn_ChannelEvidence.
  repeat constructor.
  - change (Lean.eq (gateway_shared_descriptors table (Nat_of_nat 0))
      (Option_some_inst1 _ (gateway_shared_descriptor data))).
    unfold gateway_shared_descriptors; rewrite nat2Natid; change (Z.of_nat 0) with 0; rewrite INPUT; constructor.
  - change (Lean.eq (gateway_shared_descriptors table (Nat_of_nat 1))
      (Option_some_inst1 _ (gateway_shared_descriptor data))).
    unfold gateway_shared_descriptors; rewrite nat2Natid; change (Z.of_nat 1) with 1; rewrite OUTPUT; constructor.
  - change (Lean.eq (gateway_shared_descriptors table (Nat_of_nat 3))
      (Option_some_inst1 _ (gateway_shared_descriptor control))).
    unfold gateway_shared_descriptors; rewrite nat2Natid; change (Z.of_nat 3) with 3; rewrite CANCELLATION; constructor.
  - change (Lean.eq (if gateway_descriptor_cloexec data then Bool_true else Bool_false) Bool_false).
    rewrite DATA_FLAGS; constructor.
  - change (Lean.eq (if gateway_descriptor_cloexec control then Bool_true else Bool_false) Bool_false).
    rewrite CONTROL_FLAGS; constructor.
  - change (Ne Lean.Nat (Nat_of_nat (gateway_resource_object (gateway_descriptor_object data)))
      (Nat_of_nat (gateway_resource_object (gateway_descriptor_object control)))).
    apply gateway_shared_nat_separate; exact SEPARATE.
Qed.
