(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.encoding: Exact byte layout from actual sequential source updates. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import Writers DecoderValidity FrameRecord BytePatch
  SenderEncodingPrefix SenderEncodingTail PatchLayout.
Import ListNotations.
Definition sender_header_fields sequence r :=
  frame_magic ++ [Byte.repr 1;Byte.zero;Byte.repr (Int.unsigned (fr_kind r));Byte.zero] ++
  frame_word64 (fr_run r) ++ frame_word64 sequence ++ frame_word32 (Int.repr 128) ++ repeat Byte.zero 4 ++
  frame_word32 (fr_stage r) ++ frame_word32 (fr_detail r) ++ frame_word32 (fr_entry r) ++
  frame_word32 (fr_clean r) ++ frame_word32 (fr_triggers r) ++ frame_word32 (fr_uid r) ++
  frame_word64 (fr_cpu r) ++ frame_word64 (fr_peak r) ++ frame_word64 (fr_out r) ++
  frame_word64 (fr_err r) ++ frame_word64 (fr_elapsed r) ++
  frame_word32 (fr_export_state r) ++ frame_word32 (fr_omitted r).

Theorem sender_prefix_exact : forall sequence r,
  sender_prefix_bytes sequence r=sender_header_fields sequence r ++ repeat Byte.zero 56.
Proof.
  intros;unfold sender_prefix_bytes,sender_header_fields,sender_magic_bytes,
    frame_word32,frame_word64,put32_values,put64_values,frame_magic.
  cbn [fold_left fst snd patch_bytes firstn skipn map app repeat length Nat.add]. reflexivity.
Qed.
Theorem sender_prefix_length : forall sequence r,length (sender_prefix_bytes sequence r)=160%nat.
Proof.
  intros;rewrite sender_prefix_exact;unfold sender_header_fields;
    rewrite !app_length,!frame_word32_length,!frame_word64_length,!repeat_length;reflexivity.
Qed.
Lemma sender_header_fields_length : forall sequence r,length (sender_header_fields sequence r)=104%nat.
Proof.
  intros;unfold sender_header_fields;rewrite !app_length,!frame_word32_length,!frame_word64_length,!repeat_length;reflexivity.
Qed.
Theorem sender_tail_exact : forall sequence r digest,
  length digest=32%nat -> sender_tail_bytes sequence r digest=outgoing_frame sequence r digest.
Proof.
  intros sequence r digest LEN. unfold sender_tail_bytes;rewrite sender_prefix_exact.
  pose proof (patch_zero_tail (sender_header_fields sequence r) digest 24) as FIRST.
  rewrite LEN,sender_header_fields_length in FIRST;cbn [Nat.add] in FIRST;rewrite FIRST.
  pose proof (patch_zero_tail (sender_header_fields sequence r++digest) (frame_word64 (fr_oom r)) 16) as OOM.
  rewrite app_length,sender_header_fields_length,LEN,frame_word64_length in OOM;cbn [Nat.add] in OOM.
  rewrite <- !app_assoc in OOM;rewrite OOM.
  pose proof (patch_zero_tail ((sender_header_fields sequence r++digest)++frame_word64 (fr_oom r))
    (frame_word64 (fr_pids r)) 8) as PIDS.
  rewrite !app_length,sender_header_fields_length,LEN,!frame_word64_length in PIDS;cbn [Nat.add] in PIDS.
  rewrite <- !app_assoc in PIDS;rewrite PIDS.
  pose proof (patch_zero_tail (((sender_header_fields sequence r++digest)++frame_word64 (fr_oom r))++frame_word64 (fr_pids r))
    (frame_word32 (fr_export_error r)) 4) as ERROR.
  rewrite !app_length,sender_header_fields_length,LEN,!frame_word64_length,frame_word32_length in ERROR;cbn [Nat.add] in ERROR.
  rewrite <- !app_assoc in ERROR;rewrite ERROR.
  unfold sender_header_fields,outgoing_frame;rewrite <- !app_assoc;reflexivity.
Qed.
