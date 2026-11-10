(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual scalar words produce the unchanged shared response framing. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewayImport GatewayWordData GatewayWordReceipt GatewayWordValues GatewayValue
  GatewayPrimitiveEncoding GatewayScalarLength.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Definition gateway_wire_append:=HAppend_hAppend_inst7(List_inst1 Nat)(List_inst1 Nat)(List_inst1 Nat)
  (instHAppendOfAppend_inst1(List_inst1 Nat)(List_instAppend_inst1 Nat)).

Lemma gateway_imported_nats_append first second :
  gateway_imported_nats(first++second)=gateway_wire_append(gateway_imported_nats first)(gateway_imported_nats second).
Proof.
  induction first as[|byte rest IH];[reflexivity|].
  change(List_cons_inst1 Nat(Nat_of_nat byte)(gateway_imported_nats(rest++second))=
    List_cons_inst1 Nat(Nat_of_nat byte)(gateway_wire_append(gateway_imported_nats rest)(gateway_imported_nats second))).
  rewrite IH;reflexivity.
Qed.

Lemma gateway_wire_bytes_append first second :
  gateway_wire_bytes(first++second)=gateway_wire_append(gateway_wire_bytes first)(gateway_wire_bytes second).
Proof. unfold gateway_wire_bytes,gateway_byte_naturals;rewrite map_app;apply gateway_imported_nats_append. Qed.

Lemma gateway_wire_bytes_length bytes :List_length_inst1 Nat(gateway_wire_bytes bytes)=Nat_of_nat(length bytes).
Proof. unfold gateway_wire_bytes,gateway_byte_naturals;rewrite gateway_shared_length,length_map;reflexivity. Qed.

Theorem gateway_scalar_source_encoding scalar byte size_bytes payload :
  Byte.unsigned byte=gateway_scalar_code scalar ->
  length size_bytes=Z.to_nat(Int.unsigned(gateway_scalar_width scalar)) ->
  gateway_decoded_value size_bytes=Z.of_nat(length payload) ->
  LeanCage_Host_GatewayResponseWords_SourceEncoded
    (LeanCage_Host_GatewayResponseCode_Subject_value(gateway_wire_scalar(Z.to_nat(gateway_scalar_code scalar))payload))
    (gateway_wire_bytes(byte::(size_bytes++payload))).
Proof.
  intros TAG WIDTH VALUE.
  change(LeanCage_Host_GatewayResponseWords_SourceEncoded
    (LeanCage_Host_GatewayResponseCode_Subject_value(gateway_wire_scalar(Z.to_nat(gateway_scalar_code scalar))payload))
    (gateway_wire_bytes(([byte]++size_bytes)++payload))).
  rewrite !gateway_wire_bytes_append.
  pose proof(gateway_decoded_encoding size_bytes)as SIZE;rewrite WIDTH,VALUE,Nat2Z.id in SIZE.
  destruct scalar; eapply LeanCage_Host_GatewayResponseWords_SourceEncoded_scalar.
  all:try solve[exact(gateway_actual_tag_encoding byte 3 TAG)|exact(gateway_actual_tag_encoding byte 4 TAG)|
    exact(gateway_actual_tag_encoding byte 5 TAG)|exact(gateway_actual_tag_encoding byte 6 TAG)|exact(gateway_actual_tag_encoding byte 9 TAG)].
  all:lazymatch goal with
  | |-LT_lt_inst1 Nat instLTNat ?code _=>
      vm_compute;repeat constructor
  | |-LeanCage_Host_GatewayWords_Encoding _ _ _=>rewrite gateway_wire_bytes_length;exact SIZE
  end.
Qed.
