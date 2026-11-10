(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Actual writer word receipts imply the native header inputs. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewayImport GatewayWordData GatewayWordReceipt GatewayWordValues GatewayResponseWord GatewayResponseLiteral
  GatewayResponseValidated.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Lemma gateway_header_imported_equality A(a b:A):Lean.eq a b->a=b.
Proof. intro SAME;destruct SAME;reflexivity. Qed.

Theorem gateway_response_encoded_word width value bytes:
  LeanCage_Host_GatewayWords_Encoding(Nat_of_nat width)(Nat_of_nat value)
    (gateway_imported_nats(gateway_byte_naturals bytes))->
  length bytes=width /\gateway_decoded_value bytes=Z.of_nat value.
Proof.
  intros[SIZE[BOUNDS DECODE]].
  pose proof(gateway_header_imported_equality _ _ _ SIZE)as LENGTH.
  pose proof(gateway_header_imported_equality _ _ _ DECODE)as VALUE.
  rewrite gateway_shared_length in LENGTH;unfold gateway_byte_naturals in LENGTH;rewrite length_map in LENGTH.
  apply(f_equal nat_of_Nat)in LENGTH;rewrite !nat2Natid in LENGTH.
  split;[exact LENGTH|].
  unfold gateway_decoded_value;rewrite VALUE,nat2Natid;reflexivity.
Qed.

Lemma gateway_response_middle {A}(first middle last:list A):
  firstn(length middle)(skipn(length first)(first++middle++last))=middle.
Proof.
  rewrite skipn_app,skipn_all,Nat.sub_diag;cbn[app skipn].
  rewrite firstn_app,firstn_all,Nat.sub_diag;cbn[firstn];apply app_nil_r.
Qed.
Lemma gateway_response_last {A}(first last:list A):
  firstn(length last)(skipn(length first)(first++last))=last.
Proof. rewrite skipn_app,skipn_all,Nat.sub_diag;cbn[app skipn];apply firstn_all. Qed.

(* The byte equality must come from the same engine write/private queue as the
   observed receive. Word equations are the unchanged strict shared interface. *)
Theorem gateway_response_layout_from_writer_words bytes status remaining status_bytes reserved_bytes size_bytes:
  bytes=gateway_response_magic++status_bytes++reserved_bytes++size_bytes->
  LeanCage_Host_GatewayWords_Encoding(Nat_of_nat 4)(Nat_of_nat(Z.to_nat(Int64.unsigned status)))
    (gateway_imported_nats(gateway_byte_naturals status_bytes))->
  LeanCage_Host_GatewayWords_Encoding(Nat_of_nat 4)(Nat_of_nat 0)
    (gateway_imported_nats(gateway_byte_naturals reserved_bytes))->
  LeanCage_Host_GatewayWords_Encoding(Nat_of_nat 8)(Nat_of_nat(Z.to_nat(Int64.unsigned remaining)))
    (gateway_imported_nats(gateway_byte_naturals size_bytes))->
  Int64.unsigned status<=3->Int64.unsigned remaining<=536870912->
  Z.of_nat(length bytes)=24 /\gateway_response_header_layout bytes status remaining.
Proof.
  intros BYTES STATUS RESERVED SIZE STATUS_BOUND SIZE_BOUND.
  destruct(gateway_response_encoded_word 4(Z.to_nat(Int64.unsigned status))status_bytes STATUS)as[STATUS_LENGTH STATUS_VALUE].
  destruct(gateway_response_encoded_word 4 0 reserved_bytes RESERVED)as[RESERVED_LENGTH RESERVED_VALUE].
  destruct(gateway_response_encoded_word 8(Z.to_nat(Int64.unsigned remaining))size_bytes SIZE)as[SIZE_LENGTH SIZE_VALUE].
  assert(MAGIC_LENGTH:length gateway_response_magic=8%nat)by reflexivity.
  assert(STATUS_BYTES:gateway_response_word_bytes bytes 8 4=status_bytes).
  { unfold gateway_response_word_bytes;rewrite BYTES.
    rewrite<-(MAGIC_LENGTH),<-(STATUS_LENGTH);apply gateway_response_middle. }
  assert(RESERVED_BYTES:gateway_response_word_bytes bytes 12 4=reserved_bytes).
  { unfold gateway_response_word_bytes;rewrite BYTES,app_assoc.
    replace 12%nat with(length(gateway_response_magic++status_bytes))by(rewrite length_app,MAGIC_LENGTH,STATUS_LENGTH;reflexivity).
    rewrite<-RESERVED_LENGTH;apply gateway_response_middle. }
  assert(SIZE_BYTES:gateway_response_word_bytes bytes 16 8=size_bytes).
  { unfold gateway_response_word_bytes;rewrite BYTES,!app_assoc.
    replace 16%nat with(length((gateway_response_magic++status_bytes)++reserved_bytes))by
      (rewrite !length_app,MAGIC_LENGTH,STATUS_LENGTH,RESERVED_LENGTH;reflexivity).
    rewrite<-SIZE_LENGTH;apply gateway_response_last. }
  split.
  - rewrite BYTES,!length_app,MAGIC_LENGTH,STATUS_LENGTH,RESERVED_LENGTH,SIZE_LENGTH;reflexivity.
  - constructor.
    + rewrite BYTES;reflexivity.
    + unfold gateway_response_word_value;rewrite STATUS_BYTES.
      change(Vlong(Int64.repr(gateway_decoded_value status_bytes))=Vlong status).
      rewrite STATUS_VALUE,Z2Nat.id,Int64.repr_unsigned;[reflexivity|pose proof(Int64.unsigned_range status);lia].
    + unfold gateway_response_word_value;rewrite SIZE_BYTES.
      change(Vlong(Int64.repr(gateway_decoded_value size_bytes))=Vlong remaining).
      rewrite SIZE_VALUE,Z2Nat.id,Int64.repr_unsigned;[reflexivity|pose proof(Int64.unsigned_range remaining);lia].
    + unfold gateway_response_word_value;rewrite RESERVED_BYTES.
      change(Vlong(Int64.repr(gateway_decoded_value reserved_bytes))=Vlong Int64.zero).
      rewrite RESERVED_VALUE;reflexivity.
    + exact STATUS_BOUND.
    + exact SIZE_BOUND.
Qed.
