(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-wire.private: Private acceptance stated directly over sender fields. *)
From Coq Require Import ZArith List Bool.
From compcert Require Import Integers.
Require Import Readers FrameBytes FrameRecord DecoderCommon DecoderTags DecoderValidity
  WireWords WireFields WireSpans WireZeros WireLayout.
Open Scope Z_scope.
Definition wire_common_valid r uid :=
  negb(Int.ltu(Int.repr 7)(Int.zero_ext 8(fr_kind r))) &&
  negb(Int.ltu(Int.repr 2)(fr_entry r)) && negb(Int.ltu(Int.repr 1)(fr_clean r)) &&
  Int.eq(fr_uid r)uid && Int.eq(fr_triggers r)Int.zero &&
  Int64.eq(fr_cpu r)Int64.zero && Int64.eq(fr_peak r)Int64.zero &&
  Int64.eq(fr_out r)Int64.zero && Int64.eq(fr_err r)Int64.zero.
Definition wire_tag_valid r preflight :=
  match Int.unsigned(Int.zero_ext 8(fr_kind r))with
  |0=>Int.eq(fr_stage r)Int.zero && negb(Int.ltu(Int.repr 255)(fr_detail r)) && Int.eq(fr_entry r)Int.one
  |1=>negb(Int.ltu(fr_stage r)Int.one) && negb(Int.ltu(Int.repr 8)(fr_stage r)) &&
      negb(Int.eq(fr_detail r)Int.zero) && negb(Int.ltu(Int.repr 4095)(fr_detail r)) && Int.eq(fr_entry r)Int.zero
  |2=>Int.eq(fr_stage r)Int.zero && negb(Int.eq(fr_detail r)Int.zero) &&
      negb(Int.ltu(Int.repr 64)(fr_detail r)) && Int.eq(fr_entry r)Int.one
  |4=>Int.eq(fr_stage r)(Int.repr 9) && negb(Int.eq(fr_detail r)Int.zero) &&
      negb(Int.ltu(Int.repr 4095)(fr_detail r))
  |5=>Int.eq(fr_stage r)Int.zero && Int.eq(fr_detail r)Int.zero && Int.eq(fr_entry r)Int.zero &&
      Int.eq(fr_clean r)Int.zero && negb(Int64.eq(fr_elapsed r)Int64.zero)
  |6=>Int.eq(fr_stage r)(Int.repr 8) && Int.eq(fr_detail r)Int.zero && Int.eq(fr_entry r)Int.one &&
      Int.eq(fr_clean r)Int.zero
  |7=>negb(Int.eq preflight Int.zero) && Int.eq(fr_stage r)Int.zero &&
      Int.eq(fr_detail r)Int.zero && Int.eq(fr_entry r)Int.zero
  |_=>false
  end.
Definition wire_accepts sequence r digest run uid preflight expected_sequence :=
  (Int64.eq(fr_run r)run && Int64.eq sequence expected_sequence) &&
    wire_common_valid r uid && wire_tail_valid r digest && wire_tag_valid r preflight.
Theorem wire_header_exact : forall sequence r digest run expected_sequence,
  length digest=32%nat ->
  header_valid(outgoing_frame sequence r digest)run expected_sequence=
    (Int64.eq(fr_run r)run && Int64.eq sequence expected_sequence).
Proof.
  intros sequence r digest run expected_sequence LEN.
  assert(MAGIC : magic_matches(outgoing_frame sequence r digest)=true).
  { unfold magic_matches;rewrite wire_first_four;reflexivity. }
  destruct(wire_fixed_bytes sequence r digest)as[B4[B5 B7]].
  unfold header_valid,header_prefix.
  rewrite MAGIC,B4,B5,B7,wire_run,wire_sequence,wire_payload,wire_reserved,wire_terminal_check by exact LEN.
  rewrite !Int.eq_true;cbn [andb];rewrite !andb_true_r;reflexivity.
Qed.
Theorem wire_common_exact : forall sequence r digest uid,
  common_valid(outgoing_frame sequence r digest)uid=wire_common_valid r uid.
Proof.
  intros;unfold common_valid,wire_common_valid.
  rewrite wire_kind,wire_entry,wire_clean,wire_uid,wire_triggers,wire_cpu,wire_peak,wire_out,wire_err;reflexivity.
Qed.
Theorem wire_tag_exact : forall sequence r digest preflight,
  tag_valid(outgoing_frame sequence r digest)preflight=wire_tag_valid r preflight.
Proof.
  intros;unfold tag_valid,wire_tag_valid;rewrite wire_kind,wire_stage,wire_detail,wire_entry,wire_clean,wire_elapsed;reflexivity.
Qed.
Theorem wire_decoder_acceptance : forall sequence r digest run uid preflight expected_sequence,
  length digest=32%nat ->
  decoder_accepts(outgoing_frame sequence r digest)run uid preflight expected_sequence=
    wire_accepts sequence r digest run uid preflight expected_sequence.
Proof.
  intros;unfold decoder_accepts,wire_accepts.
  rewrite wire_header_exact,wire_common_exact,wire_reserved_check,wire_tag_exact by assumption;reflexivity.
Qed.
