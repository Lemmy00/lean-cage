(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Source-decoded UInt64 values do not hide modular overflow. *)
From Stdlib Require Import ZArith Lia List.
From compcert Require Import Coqlib Integers.
From LeanImport Require Import Lean.
Require Import Readers.
From HostGateway Require Import GatewayImport GatewayWordData GatewayWordReceipt GatewayWordsMath.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Definition gateway_decoded_value bytes :Z:=Z.of_nat(nat_of_Nat(LeanCage_Host_GatewayWords_decode
  (gateway_imported_nats(gateway_byte_naturals bytes)))).

Lemma gateway_raw_byte_words_bounded bytes :
  Forall(fun value=>0<=Int.unsigned value<256)(map Readers.byte_word bytes).
Proof.
  apply Forall_forall;intros value MEMBER;apply in_map_iff in MEMBER.
  destruct MEMBER as[byte[SAME MEMBER]];subst value;unfold Readers.byte_word.
  rewrite Int.unsigned_repr;[pose proof(Byte.unsigned_range byte);change Byte.modulus with 256 in *;lia|].
  pose proof(Byte.unsigned_range byte);change Byte.modulus with 256 in *;
    change Int.max_unsigned with 4294967295;lia.
Qed.

Lemma gateway_raw_byte_word_naturals bytes :
  gateway_int_bytes(map Readers.byte_word bytes)=gateway_byte_naturals bytes.
Proof.
  unfold gateway_int_bytes,gateway_byte_naturals;rewrite map_map;apply map_ext;intro byte.
  unfold Readers.byte_word;rewrite Int.unsigned_repr;[reflexivity|].
  pose proof(Byte.unsigned_range byte);change Byte.modulus with 256 in *;
    change Int.max_unsigned with 4294967295;lia.
Qed.

Lemma gateway_decoded_value_numeric bytes :
  gateway_decoded_value bytes=Z.of_nat(gateway_natural_decode(gateway_byte_naturals bytes)).
Proof. unfold gateway_decoded_value;rewrite gateway_shared_decode;reflexivity. Qed.

Theorem gateway_decoded_value_bound bytes :
  (length bytes<=8)%nat ->0<=gateway_decoded_value bytes<=Int64.max_unsigned.
Proof.
  intro WIDTH.
  pose proof(gateway_decode_bound _ (gateway_raw_byte_words_bounded bytes))as RANGE.
  rewrite gateway_raw_byte_word_naturals,length_map,<-gateway_decoded_value_numeric in RANGE.
  pose proof(two_p_monotone(8*Z.of_nat(length bytes))64 ltac:(lia))as MAXIMUM.
  change(two_p 64)with 18446744073709551616 in MAXIMUM.
  change Int64.max_unsigned with 18446744073709551615;lia.
Qed.

Theorem gateway_decoded_unsigned bytes :
  (length bytes<=8)%nat ->Int64.unsigned(Int64.repr(gateway_decoded_value bytes))=gateway_decoded_value bytes.
Proof. intro WIDTH;apply Int64.unsigned_repr;apply gateway_decoded_value_bound;exact WIDTH. Qed.

Theorem gateway_decoded_single byte :gateway_decoded_value[byte]=Byte.unsigned byte.
Proof.
  rewrite gateway_decoded_value_numeric.
  change(Z.of_nat(Z.to_nat(Byte.unsigned byte)+256*0)=Byte.unsigned byte)%nat.
  rewrite Nat.mul_0_r,Nat.add_0_r,Z2Nat.id;[reflexivity|pose proof(Byte.unsigned_range byte);lia].
Qed.

Theorem gateway_decoded_encoding bytes :
  LeanCage_Host_GatewayWords_Encoding(Nat_of_nat(length bytes))
    (Nat_of_nat(Z.to_nat(gateway_decoded_value bytes)))
    (gateway_imported_nats(gateway_byte_naturals bytes)).
Proof.
  apply gateway_shared_encoding.
  - unfold gateway_byte_naturals;rewrite length_map;reflexivity.
  - apply Forall_forall;intros value MEMBER;unfold gateway_byte_naturals in MEMBER;apply in_map_iff in MEMBER.
    destruct MEMBER as[byte[SAME MEMBER]];subst value.
    pose proof(Byte.unsigned_range byte)as RANGE;change Byte.modulus with 256 in RANGE;lia.
  - rewrite gateway_decoded_value_numeric,Nat2Z.id;reflexivity.
Qed.
