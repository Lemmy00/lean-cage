(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual child byte segments compose the unchanged shared
   container framing and its checked four-byte count. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewayImport GatewayValue GatewayWordData GatewayWordReceipt GatewayWordValues
  GatewayPrimitiveEncoding GatewayScalarEncoding GatewayContainerLength.
Import ListNotations.
Local Close Scope lean_scope.

Inductive gateway_response_frame(subject:LeanCage_Host_GatewayResponseCode_Subject)(bytes:list Byte.int):Prop:=
|gateway_response_framed:LeanCage_Host_GatewayResponseWords_SourceEncoded subject(gateway_wire_bytes bytes)->
  gateway_response_frame subject bytes.

Lemma gateway_response_frame_shared subject bytes:
  gateway_response_frame subject bytes->LeanCage_Host_GatewayResponseWords_SourceEncoded subject(gateway_wire_bytes bytes).
Proof. intros[SHARED];exact SHARED. Qed.

Lemma gateway_wire_values_length values:
  List_length_inst1 gateway_wire_value(gateway_wire_values values)=Nat_of_nat(length values).
Proof. induction values;[reflexivity|].
  change(Nat_succ(List_length_inst1 gateway_wire_value(gateway_wire_values values))=Nat_succ(Nat_of_nat(length values))).
  rewrite IHvalues;reflexivity. Qed.
Lemma gateway_wire_fields_length fields:
  List_length_inst1(Prod_inst3 gateway_wire_value gateway_wire_value)(gateway_wire_fields fields)=Nat_of_nat(length fields).
Proof. induction fields as[|[key value]rest IH];[reflexivity|].
  change(Nat_succ(List_length_inst1(Prod_inst3 gateway_wire_value gateway_wire_value)(gateway_wire_fields rest))=
    Nat_succ(Nat_of_nat(length rest))). rewrite IH;reflexivity. Qed.

Theorem gateway_value_segments_framed values chunks:
  Forall2(fun value bytes=>gateway_response_frame(LeanCage_Host_GatewayResponseCode_Subject_value value)bytes)values chunks->
  gateway_response_frame(LeanCage_Host_GatewayResponseCode_Subject_values(gateway_wire_values values))(concat chunks).
Proof.
  intro SEGMENTS;constructor;induction SEGMENTS;cbn[gateway_wire_values concat gateway_wire_bytes gateway_byte_naturals gateway_imported_nats].
  - apply LeanCage_Host_GatewayResponseWords_SourceEncoded_valuesNil.
  - change(LeanCage_Host_GatewayResponseWords_SourceEncoded
      (LeanCage_Host_GatewayResponseCode_Subject_values(gateway_wire_values(x::l)))
      (gateway_wire_bytes(y++concat l'))).
    rewrite gateway_wire_bytes_append;apply LeanCage_Host_GatewayResponseWords_SourceEncoded_valuesCons;
      [apply gateway_response_frame_shared;exact H|exact IHSEGMENTS].
Qed.

Theorem gateway_field_segments_framed(fields:list(gateway_wire_value*gateway_wire_value))chunks:
  Forall2(fun field bytes=>exists key_bytes value_bytes,bytes=key_bytes++value_bytes /\
    gateway_response_frame(LeanCage_Host_GatewayResponseCode_Subject_value(Datatypes.fst field))key_bytes /\
    gateway_response_frame(LeanCage_Host_GatewayResponseCode_Subject_value(Datatypes.snd field))value_bytes)fields chunks->
  gateway_response_frame(LeanCage_Host_GatewayResponseCode_Subject_fields(gateway_wire_fields fields))(concat chunks).
Proof.
  intro SEGMENTS;constructor;induction SEGMENTS;cbn[gateway_wire_fields concat gateway_wire_bytes gateway_byte_naturals gateway_imported_nats].
  - apply LeanCage_Host_GatewayResponseWords_SourceEncoded_fieldsNil.
  - destruct x as[key value];destruct H as[key_bytes[value_bytes[BYTES[KEY VALUE]]]];subst y.
    change(LeanCage_Host_GatewayResponseWords_SourceEncoded
      (LeanCage_Host_GatewayResponseCode_Subject_fields(gateway_wire_fields((key,value)::l)))
      (gateway_wire_bytes((key_bytes++value_bytes)++concat l'))).
    rewrite !gateway_wire_bytes_append;apply LeanCage_Host_GatewayResponseWords_SourceEncoded_fieldsCons;
      [apply gateway_response_frame_shared;exact KEY|apply gateway_response_frame_shared;exact VALUE|exact IHSEGMENTS].
Qed.

Theorem gateway_array_source_framing byte count_bytes values body:
  Byte.unsigned byte=7->length count_bytes=4%nat->gateway_decoded_value count_bytes=Z.of_nat(length values)->
  gateway_response_frame(LeanCage_Host_GatewayResponseCode_Subject_values(gateway_wire_values values))body->
  gateway_response_frame(LeanCage_Host_GatewayResponseCode_Subject_value
    (LeanCage_Host_GatewayResponseCode_Value_array(gateway_wire_values values)))(byte::(count_bytes++body)).
Proof.
  intros TAG WIDTH COUNT BODY;constructor.
  change(LeanCage_Host_GatewayResponseWords_SourceEncoded
    (LeanCage_Host_GatewayResponseCode_Subject_value(LeanCage_Host_GatewayResponseCode_Value_array(gateway_wire_values values)))
    (gateway_wire_bytes(([byte]++count_bytes)++body))).
  rewrite !gateway_wire_bytes_append;eapply LeanCage_Host_GatewayResponseWords_SourceEncoded_array.
  - exact(gateway_actual_tag_encoding byte 7 TAG).
  - rewrite gateway_wire_values_length;pose proof(gateway_decoded_encoding count_bytes)as WORD;rewrite WIDTH,COUNT,Nat2Z.id in WORD;exact WORD.
  - apply gateway_response_frame_shared;exact BODY.
Qed.

Theorem gateway_object_source_framing byte count_bytes fields body:
  Byte.unsigned byte=8->length count_bytes=4%nat->gateway_decoded_value count_bytes=Z.of_nat(length fields)->
  gateway_response_frame(LeanCage_Host_GatewayResponseCode_Subject_fields(gateway_wire_fields fields))body->
  gateway_response_frame(LeanCage_Host_GatewayResponseCode_Subject_value
    (LeanCage_Host_GatewayResponseCode_Value_object(gateway_wire_fields fields)))(byte::(count_bytes++body)).
Proof.
  intros TAG WIDTH COUNT BODY;constructor.
  change(LeanCage_Host_GatewayResponseWords_SourceEncoded
    (LeanCage_Host_GatewayResponseCode_Subject_value(LeanCage_Host_GatewayResponseCode_Value_object(gateway_wire_fields fields)))
    (gateway_wire_bytes(([byte]++count_bytes)++body))).
  rewrite !gateway_wire_bytes_append;eapply LeanCage_Host_GatewayResponseWords_SourceEncoded_object.
  - exact(gateway_actual_tag_encoding byte 8 TAG).
  - rewrite gateway_wire_fields_length;pose proof(gateway_decoded_encoding count_bytes)as WORD;rewrite WIDTH,COUNT,Nat2Z.id in WORD;exact WORD.
  - apply gateway_response_frame_shared;exact BODY.
Qed.
