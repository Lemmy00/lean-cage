(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Real count and depth widths bound the recursive source loop arithmetic. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers.
Require Import Readers.
From HostGateway Require Import GatewayWordValues GatewayWordData GatewayWordsMath GatewayContainerLength GatewayContainerGuards.
Open Scope Z_scope.

Lemma gateway_container_word_count bytes :
  length bytes=4%nat ->0<=gateway_decoded_value bytes<4294967296 /\
    Int64.unsigned(Int64.repr(gateway_decoded_value bytes))=gateway_decoded_value bytes.
Proof.
  intro WIDTH.
  pose proof(gateway_decode_bound _ (gateway_raw_byte_words_bounded bytes))as RANGE.
  rewrite gateway_raw_byte_word_naturals,length_map,<-gateway_decoded_value_numeric,WIDTH in RANGE.
  change(0<=gateway_decoded_value bytes<4294967296)in RANGE;split;[exact RANGE|].
  apply gateway_decoded_unsigned;lia.
Qed.

Lemma gateway_container_next_index index size :
  0<=Int64.unsigned index<Int64.unsigned size ->Int64.unsigned size<4294967296 ->
  Int64.unsigned(Int64.add index Int64.one)=Int64.unsigned index+1.
Proof.
  intros POSITION SIZE;unfold Int64.add;rewrite Int64.unsigned_one.
  apply Int64.unsigned_repr;change Int64.max_unsigned with 18446744073709551615;lia.
Qed.

Lemma gateway_container_child_depth depth :
  depth<>Int.zero ->Int.unsigned(Int.sub depth Int.one)=Int.unsigned depth-1.
Proof.
  intro NONZERO.
  assert(POSITIVE:0<Int.unsigned depth).
  { pose proof(Int.unsigned_range depth);destruct(Z.eq_dec(Int.unsigned depth)0);[|lia].
    exfalso;apply NONZERO;rewrite<-(Int.repr_unsigned depth),e;reflexivity. }
  unfold Int.sub;rewrite Int.unsigned_one;apply Int.unsigned_repr.
  pose proof(Int.unsigned_range_2 depth);lia.
Qed.

Lemma gateway_container_capacity_value container nodes :
  Int64.unsigned(gateway_container_capacity container nodes)=
    match container with gateway_container_array=>Int64.unsigned nodes|gateway_container_object=>Int64.unsigned nodes/2 end.
Proof.
  destruct container;[reflexivity|]. cbn[gateway_container_capacity];unfold Int64.divu.
  change(Int64.unsigned(Int64.repr(Int64.unsigned nodes/2))=Int64.unsigned nodes/2).
  apply Int64.unsigned_repr;split.
  - apply Z.div_pos;[pose proof(Int64.unsigned_range nodes);lia|lia].
  - eapply Z.le_trans with(m:=Int64.unsigned nodes);[apply Z.div_le_upper_bound;[lia|pose proof(Int64.unsigned_range nodes);lia]|].
    exact(proj2(Int64.unsigned_range_2 nodes)).
Qed.
