(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Current source-held descriptor/OFD
   operands produce the shared receive data on the same physical row. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers Values.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewayNativeImport GatewayNativeWords GatewayNativeRows GatewayNativeReferences
  GatewayNativeStreamObservation GatewayNativeCallOperands GatewayChannelCodeProducer GatewayChannelSourceScope GatewaySpawnResources GatewaySpawnDescriptors.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.
Module ND := GatewayNativeImport.
Local Opaque Nat_of_nat Z.to_nat.

Definition gateway_channel_receive_use environment before allocated
    (storage : gateway_channel_storage environment before allocated) process position selected row
    descriptor amount (entry : gateway_resource_descriptor) bytes :=
  ND.LeanCage_Host_ChannelCode_ReceiveUse_mk
    (gateway_channel_invocation _ _ _ storage process position) (Nat_of_nat selected) row
    (Nat_of_nat (Z.to_nat (Int.signed descriptor))) (Nat_of_nat (Z.to_nat amount))
    (Nat_of_nat (gateway_resource_object (gateway_descriptor_object entry)))
    (Nat_of_nat (gateway_resource_description (gateway_descriptor_object entry)))
    (gateway_native_bytes bytes).

Lemma gateway_channel_receive_use_consistent environment before allocated
    (storage : gateway_channel_storage environment before allocated) process position selected row
    descriptor amount entry bytes :
  gateway_native_row_process row = Nat_of_nat process -> (position <= selected)%nat ->
  0 <= Int.signed descriptor <= Int.max_signed -> 0 < amount <= 65536 ->
  gateway_native_row_operation row = gateway_native_receive_code descriptor (Int64.repr amount) Int.zero ->
  gateway_native_lease_at (gateway_native_row_input row) (Int.signed descriptor) entry ->
  gateway_native_stream_product row ND.LeanCage_Host_NativeCode_Product_received bytes ->
  ND.LeanCage_Host_ChannelCode_ReceiveUse_Consistent
    (gateway_channel_receive_use _ _ _ storage process position selected row descriptor amount entry bytes).
Proof.
  intros PROCESS ORDER DESCRIPTOR AMOUNT CODE INPUT PRODUCT.
  assert (DESCRIPTOR_WORD : gateway_native_int descriptor = Nat_of_nat (Z.to_nat (Int.signed descriptor))).
  { rewrite <- (Int.repr_signed descriptor) at 1; apply gateway_native_repr_int; exact DESCRIPTOR. }
  assert (EXTENT_WORD : gateway_native_word (Int64.repr amount) = Nat_of_nat (Z.to_nat amount)).
  { unfold gateway_native_word; rewrite Int64.unsigned_repr; [reflexivity |].
    change Int64.max_unsigned with 18446744073709551615; lia. }
  unfold ND.LeanCage_Host_ChannelCode_ReceiveUse_Consistent, gateway_channel_receive_use.
  cbn -[ND.LeanCage_Host_ChannelCode_Invocation_WellFormed gateway_channel_invocation Nat_of_nat Lean.double].
  apply Lean.And_intro; [apply gateway_channel_invocation_formed |].
  repeat apply Lean.And_intro.
  - change (Lean.eq (gateway_native_row_process row) (Nat_of_nat process)); rewrite PROCESS; constructor.
  - change (Lean.Nat_le (Nat_of_nat position) (Nat_of_nat selected)); apply nat_le_Nat_le'; exact ORDER.
  - apply gateway_channel_pair_bound; exact DESCRIPTOR.
  - change (Lean.Nat_le (Nat_of_nat 1) (Nat_of_nat (Z.to_nat amount))).
    apply nat_le_Nat_le'; apply Nat2Z.inj_le; rewrite Z2Nat.id by lia; lia.
  - change (ND.LE_le_inst1 Lean.Nat ND.instLENat (Nat_of_nat (Z.to_nat amount))
      (gateway_channel_positive 65536%positive)).
    apply nat_le_Nat_le; apply Nat2Z.inj_le; rewrite nat2Natid, gateway_channel_positive_value, Z2Nat.id by lia; lia.
  - change (Lean.eq (gateway_native_row_operation row)
      (ND.LeanCage_Host_NativeCode_Operation_receive
        (Nat_of_nat (Z.to_nat (Int.signed descriptor))) (Nat_of_nat (Z.to_nat amount)) Lean.Nat_zero)).
    rewrite CODE; unfold gateway_native_receive_code.
    rewrite DESCRIPTOR_WORD, EXTENT_WORD; constructor.
  - exact (gateway_channel_lease_reference _ _ _ INPUT).
  - destruct PRODUCT as [RECEIVED |[EMPTY NONE]].
    + apply Lean.Or_inl.
      change (Lean.eq (gateway_native_row_product row) (ND.LeanCage_Host_NativeCode_Product_received (gateway_native_bytes bytes))).
      rewrite RECEIVED; constructor.
    + apply Lean.Or_inr; apply Lean.And_intro.
      * rewrite EMPTY; constructor.
      * change (Lean.eq (gateway_native_row_product row) ND.LeanCage_Host_NativeCode_Product_none).
        rewrite NONE; constructor.
Qed.

Record gateway_channel_receive_checked (use : ND.LeanCage_Host_ChannelCode_ReceiveUse) : Prop := {
  gateway_channel_receive_consistent : ND.LeanCage_Host_ChannelCode_ReceiveUse_Consistent use
}.
