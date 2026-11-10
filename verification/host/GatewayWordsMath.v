(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Reuse accepted bit-exact word lemmas for actual gateway bytes. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers.
Require Import Writers Readers CodecRoundtrip Codec BridgeWords.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewayImport GatewayWordData.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Definition gateway_int_bytes (values:list int) : list nat :=
  map(fun value=>Z.to_nat(Int.unsigned value))values.

Lemma gateway_byte_unsigned value : Int.zero_ext 8 value=value -> 0<=Int.unsigned value<256.
Proof.
  intro BYTE;pose proof(Int.zero_ext_range 8 value ltac:(change(0<=8<32);lia))as RANGE.
  rewrite BYTE in RANGE;exact RANGE.
Qed.

Lemma gateway_word_byte_exact value : Int.zero_ext 8 value=value ->
  byte_word(Byte.repr(Int.unsigned value))=value.
Proof.
  intro BYTE;pose proof(gateway_byte_unsigned value BYTE)as RANGE.
  unfold byte_word;rewrite Byte.unsigned_repr by(change Byte.max_unsigned with 255;lia).
  apply Int.repr_unsigned.
Qed.

Lemma gateway_put32_byte_range value index : 0<=Int.unsigned(put32_byte value index)<256.
Proof. apply gateway_byte_unsigned;unfold put32_byte;rewrite Int.zero_ext_idem by lia;reflexivity. Qed.
Lemma gateway_put64_byte_range value index : 0<=Int.unsigned(put64_byte value index)<256.
Proof. apply gateway_byte_unsigned;unfold put64_byte;rewrite Int.zero_ext_idem by lia;reflexivity. Qed.

Theorem gateway_put32_decodes value :
  Z.of_nat(gateway_natural_decode(gateway_int_bytes(put32_values value)))=Int.unsigned value.
Proof.
  pose proof(get32_bytes_numeric
    (Byte.repr(Int.unsigned(put32_byte value 0)))(Byte.repr(Int.unsigned(put32_byte value 1)))
    (Byte.repr(Int.unsigned(put32_byte value 2)))(Byte.repr(Int.unsigned(put32_byte value 3))))as ENCODED.
  rewrite !gateway_word_byte_exact in ENCODED by
    (unfold put32_byte;rewrite Int.zero_ext_idem by lia;reflexivity).
  rewrite put_get32_word in ENCODED.
  rewrite !Byte.unsigned_repr in ENCODED by
    (match goal with|-0<=Int.unsigned(put32_byte _ ?index)<=_=>
      pose proof(gateway_put32_byte_range value index);change Byte.max_unsigned with 255;lia end).
  apply(f_equal Int.unsigned)in ENCODED.
  rewrite Int.unsigned_repr in ENCODED by
    (change Int.max_unsigned with 4294967295;
     pose proof(gateway_put32_byte_range value 0);pose proof(gateway_put32_byte_range value 1);
     pose proof(gateway_put32_byte_range value 2);pose proof(gateway_put32_byte_range value 3);lia).
  cbn[put32_values gateway_int_bytes gateway_natural_decode map fold_right].
  repeat first[rewrite Nat2Z.inj_add|rewrite Nat2Z.inj_mul].
  rewrite !Z2Nat.id by(match goal with|-0<=Int.unsigned ?word=>pose proof(Int.unsigned_range word);lia end).
  cbn[Z.of_nat].
  lia.
Qed.

Theorem gateway_put64_decodes value :
  Z.of_nat(gateway_natural_decode(gateway_int_bytes(put64_values value)))=Int64.unsigned value.
Proof.
  pose proof(get64_bytes_numeric
    (Byte.repr(Int.unsigned(put64_byte value 0)))(Byte.repr(Int.unsigned(put64_byte value 1)))
    (Byte.repr(Int.unsigned(put64_byte value 2)))(Byte.repr(Int.unsigned(put64_byte value 3)))
    (Byte.repr(Int.unsigned(put64_byte value 4)))(Byte.repr(Int.unsigned(put64_byte value 5)))
    (Byte.repr(Int.unsigned(put64_byte value 6)))(Byte.repr(Int.unsigned(put64_byte value 7))))as ENCODED.
  rewrite !gateway_word_byte_exact in ENCODED by
    (unfold put64_byte;rewrite Int.zero_ext_idem by lia;reflexivity).
  rewrite put_get64_word in ENCODED.
  rewrite !Byte.unsigned_repr in ENCODED by
    (match goal with|-0<=Int.unsigned(put64_byte _ ?index)<=_=>
      pose proof(gateway_put64_byte_range value index);change Byte.max_unsigned with 255;lia end).
  apply(f_equal Int64.unsigned)in ENCODED.
  rewrite Int64.unsigned_repr in ENCODED by
    (change Int64.max_unsigned with 18446744073709551615;
     pose proof(gateway_put64_byte_range value 0);pose proof(gateway_put64_byte_range value 1);
     pose proof(gateway_put64_byte_range value 2);pose proof(gateway_put64_byte_range value 3);
     pose proof(gateway_put64_byte_range value 4);pose proof(gateway_put64_byte_range value 5);
     pose proof(gateway_put64_byte_range value 6);pose proof(gateway_put64_byte_range value 7);lia).
  cbn[put64_values gateway_int_bytes gateway_natural_decode map fold_right].
  repeat first[rewrite Nat2Z.inj_add|rewrite Nat2Z.inj_mul].
  rewrite !Z2Nat.id by(match goal with|-0<=Int.unsigned ?word=>pose proof(Int.unsigned_range word);lia end).
  cbn[Z.of_nat];lia.
Qed.

Lemma gateway_int_bytes_bounded values :
  Forall(fun value=>0<=Int.unsigned value<256)values ->
  Forall(fun byte=>(byte<256)%nat)(gateway_int_bytes values).
Proof. intro BOUND;induction BOUND;constructor;[lia|exact IHBOUND]. Qed.

Theorem gateway_put32_encoding value :
  LeanCage_Host_GatewayWords_Encoding(Nat_of_nat 4)(Nat_of_nat(Z.to_nat(Int.unsigned value)))
    (gateway_imported_nats(gateway_int_bytes(put32_values value))).
Proof.
  apply gateway_shared_encoding.
  - reflexivity.
  - apply gateway_int_bytes_bounded;apply Forall_forall;intros byte MEMBER.
    unfold put32_values in MEMBER;apply in_map_iff in MEMBER.
    destruct MEMBER as[index[SAME MEMBER]];subst byte;apply gateway_put32_byte_range.
  - apply Nat2Z.inj;rewrite gateway_put32_decodes,Z2Nat.id;[reflexivity|pose proof(Int.unsigned_range value);lia].
Qed.

Theorem gateway_put64_encoding value :
  LeanCage_Host_GatewayWords_Encoding(Nat_of_nat 8)(Nat_of_nat(Z.to_nat(Int64.unsigned value)))
    (gateway_imported_nats(gateway_int_bytes(put64_values value))).
Proof.
  apply gateway_shared_encoding.
  - reflexivity.
  - apply gateway_int_bytes_bounded;apply Forall_forall;intros byte MEMBER.
    unfold put64_values in MEMBER;apply in_map_iff in MEMBER.
    destruct MEMBER as[index[SAME MEMBER]];subst byte;apply gateway_put64_byte_range.
  - apply Nat2Z.inj;rewrite gateway_put64_decodes,Z2Nat.id;[reflexivity|pose proof(Int64.unsigned_range value);lia].
Qed.

Fixpoint gateway_get_value_from (bytes:list int)(index:Z)(value:int64) : int64 :=
  match bytes with
  | []=>value
  | byte::rest=>gateway_get_value_from rest(index+1)
      (Int64.or value(Int64.shl(Int64.repr(Int.unsigned byte))(Int64.repr(8*index))))
  end.
Definition gateway_get_value bytes:=gateway_get_value_from bytes 0 Int64.zero.

Lemma gateway_decode_cons value rest :
  Z.of_nat(gateway_natural_decode(gateway_int_bytes(value::rest)))=
    Int.unsigned value+256*Z.of_nat(gateway_natural_decode(gateway_int_bytes rest)).
Proof.
  change(Z.of_nat((Z.to_nat(Int.unsigned value)+256*gateway_natural_decode(gateway_int_bytes rest))%nat)=
    Int.unsigned value+256*Z.of_nat(gateway_natural_decode(gateway_int_bytes rest))).
  rewrite Nat2Z.inj_add,Nat2Z.inj_mul,Z2Nat.id by(pose proof(Int.unsigned_range value);lia).
  reflexivity.
Qed.

Lemma gateway_get_value_prefix bytes index low :
  Forall(fun byte=>0<=Int.unsigned byte<256)bytes ->
  0<=index -> index+Z.of_nat(length bytes)<=8 -> 0<=low<two_p(8*index) ->
  gateway_get_value_from bytes index(Int64.repr low)=
    Int64.repr(low+two_p(8*index)*Z.of_nat(gateway_natural_decode(gateway_int_bytes bytes))).
Proof.
  intro BOUNDED;revert index low;induction BOUNDED as[|byte rest BYTE REST IH];
    intros index low NONNEGATIVE LENGTH LOWER.
  - change(Int64.repr low=Int64.repr(low+two_p(8*index)*0)).
    rewrite Z.mul_0_r,Z.add_0_r;reflexivity.
  - cbn[length]in LENGTH;rewrite Nat2Z.inj_succ in LENGTH.
    assert(POSITIVE:0<two_p(8*index))by(pose proof(two_p_gt_ZERO(8*index)ltac:(lia));lia).
    assert(GROW:two_p(8*(index+1))=two_p(8*index)*256).
    { replace(8*(index+1))with(8*index+8)by lia;rewrite two_p_is_exp by lia;reflexivity. }
    cbn[gateway_get_value_from].
    rewrite int64_low_shifted by lia.
    rewrite(IH(index+1)(low+Int.unsigned byte*two_p(8*index)))by
      (try lia;rewrite GROW;nia).
    rewrite GROW,gateway_decode_cons;apply(f_equal Int64.repr);ring.
Qed.

Lemma gateway_decode_bound bytes :
  Forall(fun byte=>0<=Int.unsigned byte<256)bytes ->
  0<=Z.of_nat(gateway_natural_decode(gateway_int_bytes bytes))<two_p(8*Z.of_nat(length bytes)).
Proof.
  intro BOUND;induction BOUND as[|byte rest BYTE REST IH].
  - change(0<=0<1);lia.
  - rewrite gateway_decode_cons;cbn[length];rewrite Nat2Z.inj_succ.
    replace(8*Z.succ(Z.of_nat(length rest)))with(8*Z.of_nat(length rest)+8)by lia.
    rewrite two_p_is_exp by lia;change(two_p 8)with 256;lia.
Qed.

Theorem gateway_get_value_numeric bytes :
  Forall(fun byte=>0<=Int.unsigned byte<256)bytes -> (length bytes<=8)%nat ->
  Int64.unsigned(gateway_get_value bytes)=Z.of_nat(gateway_natural_decode(gateway_int_bytes bytes)).
Proof.
  intros BOUND WIDTH.
  unfold gateway_get_value;change Int64.zero with(Int64.repr 0).
  rewrite gateway_get_value_prefix by(try exact BOUND;cbn;lia).
  change(two_p(8*0))with 1;rewrite Z.mul_1_l,Z.add_0_l.
  apply Int64.unsigned_repr.
  pose proof(gateway_decode_bound bytes BOUND)as RANGE.
  pose proof(two_p_monotone(8*Z.of_nat(length bytes))64 ltac:(lia))as MAXIMUM.
  change(two_p 64)with 18446744073709551616 in MAXIMUM.
  change Int64.max_unsigned with 18446744073709551615;lia.
Qed.
