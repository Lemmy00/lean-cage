(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-wire.private: Actual decoded fields include narrowing and tail clearing on late rejection. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers Values Memory.
Require Import ScalarMemory ResultLayout FrameBytes FrameRecord DecoderLayout WireFields.
Import ListNotations.
Open Scope Z_scope.
Definition wire_decoded_record r : frame_result :=
  {|fr_kind:=Int.zero_ext 8(fr_kind r);fr_stage:=fr_stage r;fr_detail:=fr_detail r;
    fr_entry:=fr_entry r;fr_clean:=fr_clean r;fr_triggers:=fr_triggers r;fr_uid:=fr_uid r;
    fr_run:=fr_run r;fr_cpu:=fr_cpu r;fr_peak:=fr_peak r;fr_out:=fr_out r;fr_err:=fr_err r;
    fr_elapsed:=fr_elapsed r;fr_oom:=Int64.zero;fr_pids:=Int64.zero;
    fr_export_state:=Int.zero;fr_omitted:=Int.zero;fr_export_error:=Int.zero|}.
Lemma wire_zero_nth : forall count index,
  nth index(repeat Byte.zero count)Byte.zero=Byte.zero.
Proof. induction count;intros index;destruct index;cbn;auto. Qed.
Theorem wire_decoded_cells : forall sequence r digest,
  decoded_cells(outgoing_frame sequence r digest)=
    frame_result_cells(wire_decoded_record r)(repeat Byte.zero 32).
Proof.
  intros;unfold decoded_cells,frame_result_cells;cbn [wire_decoded_record].
  rewrite wire_kind,wire_stage,wire_detail,wire_entry,wire_clean,wire_triggers,wire_uid,
    wire_run,wire_cpu,wire_peak,wire_out,wire_err,wire_elapsed.
  f_equal;apply map_ext;intros index;unfold digest_cell,frame_digest_cell;rewrite wire_zero_nth;reflexivity.
Qed.
Theorem wire_decoded_contents : forall m b ofs sequence r digest,
  decoded_contents m b ofs(outgoing_frame sequence r digest) <->
    frame_result_contents m b ofs(wire_decoded_record r)(repeat Byte.zero 32).
Proof. intros;unfold decoded_contents,frame_result_contents;rewrite wire_decoded_cells;reflexivity. Qed.
Theorem wire_kind_within_byte : forall kind,
  Int.unsigned kind<256 -> Int.zero_ext 8 kind=kind.
Proof.
  intros kind BOUND. rewrite <-(Int.repr_unsigned(Int.zero_ext 8 kind)).
  rewrite Int.zero_ext_mod by(change(0<=8<32);lia).
  change(Int.repr(Int.unsigned kind mod 256)=kind).
  rewrite Z.mod_small by(pose proof(Int.unsigned_range kind);lia). apply Int.repr_unsigned.
Qed.
