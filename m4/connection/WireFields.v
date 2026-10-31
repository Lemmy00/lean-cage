(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-wire.fields: Exact field projections of the actual outgoing frame. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import Codec Readers Writers CodecRoundtrip FrameBytes FrameRecord DecoderValidity WireWords.
Import ListNotations.
Open Scope Z_scope.
Ltac wire_projection :=
  unfold word32_at,word64_at,byte_word_at,byte_at,outgoing_frame,frame_magic,
    frame_word32,frame_word64,put32_values,put64_values;
  cbn [map app nth Nat.add];
  lazymatch goal with
  | |- get32_word _ _ _ _ = ?x =>
    transitivity(get32_word(put32_byte x 0)(put32_byte x 1)(put32_byte x 2)(put32_byte x 3));
    [f_equal;apply wire_put32_byte|apply put_get32_word]
  | |- get64_word _ _ _ _ _ _ _ _ = ?x =>
    transitivity(get64_word(put64_byte x 0)(put64_byte x 1)(put64_byte x 2)(put64_byte x 3)
      (put64_byte x 4)(put64_byte x 5)(put64_byte x 6)(put64_byte x 7));
    [f_equal;apply wire_put64_byte|apply put_get64_word]
  end.
Theorem wire_run : forall sequence r digest,
  word64_at(outgoing_frame sequence r digest)8=(fr_run r).
Proof. intros;wire_projection. Qed.
Theorem wire_sequence : forall sequence r digest,
  word64_at(outgoing_frame sequence r digest)16=(sequence).
Proof. intros;wire_projection. Qed.
Theorem wire_payload : forall sequence r digest,
  word32_at(outgoing_frame sequence r digest)24=(Int.repr 128).
Proof. intros;wire_projection. Qed.
Theorem wire_reserved : forall sequence r digest,
  word32_at(outgoing_frame sequence r digest)28=(Int.zero).
Proof. intros;reflexivity. Qed.
Theorem wire_stage : forall sequence r digest,
  word32_at(outgoing_frame sequence r digest)32=(fr_stage r).
Proof. intros;wire_projection. Qed.
Theorem wire_detail : forall sequence r digest,
  word32_at(outgoing_frame sequence r digest)36=(fr_detail r).
Proof. intros;wire_projection. Qed.
Theorem wire_entry : forall sequence r digest,
  word32_at(outgoing_frame sequence r digest)40=(fr_entry r).
Proof. intros;wire_projection. Qed.
Theorem wire_clean : forall sequence r digest,
  word32_at(outgoing_frame sequence r digest)44=(fr_clean r).
Proof. intros;wire_projection. Qed.
Theorem wire_triggers : forall sequence r digest,
  word32_at(outgoing_frame sequence r digest)48=(fr_triggers r).
Proof. intros;wire_projection. Qed.
Theorem wire_uid : forall sequence r digest,
  word32_at(outgoing_frame sequence r digest)52=(fr_uid r).
Proof. intros;wire_projection. Qed.
Theorem wire_cpu : forall sequence r digest,
  word64_at(outgoing_frame sequence r digest)56=(fr_cpu r).
Proof. intros;wire_projection. Qed.
Theorem wire_peak : forall sequence r digest,
  word64_at(outgoing_frame sequence r digest)64=(fr_peak r).
Proof. intros;wire_projection. Qed.
Theorem wire_out : forall sequence r digest,
  word64_at(outgoing_frame sequence r digest)72=(fr_out r).
Proof. intros;wire_projection. Qed.
Theorem wire_err : forall sequence r digest,
  word64_at(outgoing_frame sequence r digest)80=(fr_err r).
Proof. intros;wire_projection. Qed.
Theorem wire_elapsed : forall sequence r digest,
  word64_at(outgoing_frame sequence r digest)88=(fr_elapsed r).
Proof. intros;wire_projection. Qed.
Theorem wire_export_state : forall sequence r digest,
  word32_at(outgoing_frame sequence r digest)96=(fr_export_state r).
Proof. intros;wire_projection. Qed.
Theorem wire_omitted : forall sequence r digest,
  word32_at(outgoing_frame sequence r digest)100=(fr_omitted r).
Proof. intros;wire_projection. Qed.
Theorem wire_kind : forall sequence r digest,
  byte_word_at(outgoing_frame sequence r digest)6=Int.zero_ext 8(fr_kind r).
Proof.
  intros;unfold byte_word_at,byte_at,outgoing_frame,frame_magic;cbn [app nth];apply wire_byte_word.
Qed.
Theorem wire_first_four : forall sequence r digest,
  firstn 4(outgoing_frame sequence r digest)=frame_magic.
Proof. reflexivity. Qed.
Theorem wire_fixed_bytes : forall sequence r digest,
  byte_word_at(outgoing_frame sequence r digest)4=Int.one /\
  byte_word_at(outgoing_frame sequence r digest)5=Int.zero /\
  byte_word_at(outgoing_frame sequence r digest)7=Int.zero.
Proof. intros;repeat split;reflexivity. Qed.
Theorem wire_after_digest : forall sequence r digest,
  length digest=32%nat ->
  skipn 136(outgoing_frame sequence r digest)=
    frame_word64(fr_oom r)++frame_word64(fr_pids r)++frame_word32(fr_export_error r)++repeat Byte.zero 4.
Proof.
  intros sequence r digest LEN.
  unfold outgoing_frame.
  repeat rewrite wire_skip_past by (rewrite ?frame_word32_length,?frame_word64_length,?repeat_length,?LEN;cbn [length frame_magic];lia).
  rewrite ?frame_word32_length,?frame_word64_length,?repeat_length,?LEN.
  reflexivity.
Qed.
