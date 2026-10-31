(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-wire.fields: All bytes after the digest and the private reserved tail. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers.
Require Import Readers FrameBytes FrameRecord DecoderValidity WireWords WireFields WireSpans WireZeros.
Import ListNotations.
Open Scope Z_scope.
Definition wire_reserved_fields r digest :=
  frame_word32(fr_export_state r)++frame_word32(fr_omitted r)++digest++
  frame_word64(fr_oom r)++frame_word64(fr_pids r)++frame_word32(fr_export_error r).
Lemma wire_reserved_fields_length : forall r digest,
  length digest=32%nat -> length(wire_reserved_fields r digest)=60%nat.
Proof. intros;unfold wire_reserved_fields;rewrite !app_length,!frame_word32_length,!frame_word64_length,H;reflexivity. Qed.
Ltac wire_skip_prefix :=
  repeat rewrite wire_skip_past by
    (rewrite ?frame_word32_length,?frame_word64_length,?repeat_length;
     try match goal with H : length _=32%nat |- _ => rewrite H end;
     cbn [length frame_magic];lia);
  rewrite ?frame_word32_length,?frame_word64_length,?repeat_length;
  try match goal with H : length _=32%nat |- _ => rewrite H end;
  cbn [length frame_magic Nat.sub];cbn [skipn].
Theorem wire_reserved_suffix : forall sequence r digest,
  skipn 96(outgoing_frame sequence r digest)=wire_reserved_fields r digest++repeat Byte.zero 4.
Proof. intros;unfold outgoing_frame,wire_reserved_fields;wire_skip_prefix;rewrite !app_assoc;reflexivity. Qed.
Theorem wire_terminal_suffix : forall sequence r digest,
  length digest=32%nat -> skipn 156(outgoing_frame sequence r digest)=repeat Byte.zero 4.
Proof. intros;unfold outgoing_frame;wire_skip_prefix;reflexivity. Qed.
Theorem wire_late_fields : forall sequence r digest,
  length digest=32%nat ->
  word64_at(outgoing_frame sequence r digest)136=fr_oom r /\
  word64_at(outgoing_frame sequence r digest)144=fr_pids r /\
  word32_at(outgoing_frame sequence r digest)152=fr_export_error r.
Proof.
  intros sequence r digest LEN;split.
  - rewrite wire_word64_skip,wire_after_digest by exact LEN;apply wire_word64_head.
  - split.
    + rewrite wire_word64_skip;unfold outgoing_frame;wire_skip_prefix;apply wire_word64_head.
    + rewrite wire_word32_skip;unfold outgoing_frame;wire_skip_prefix;apply wire_word32_head.
Qed.
Definition wire_tail_valid r digest :=
  Int.eq(fr_export_state r)Int.zero && Int.eq(fr_omitted r)Int.zero && wire_zero_bytes digest &&
  Int64.eq(fr_oom r)Int64.zero && Int64.eq(fr_pids r)Int64.zero && Int.eq(fr_export_error r)Int.zero.
Theorem wire_reserved_check : forall sequence r digest,
  length digest=32%nat ->
  zero_test(outgoing_frame sequence r digest)96 156=wire_tail_valid r digest.
Proof.
  intros sequence r digest LEN.
  change(zero_test(outgoing_frame sequence r digest)96(96+60)=wire_tail_valid r digest).
  rewrite wire_zero_span by(rewrite outgoing_frame_length by exact LEN;lia).
  rewrite wire_reserved_suffix,firstn_app,wire_reserved_fields_length by exact LEN.
  rewrite firstn_all2 by(rewrite wire_reserved_fields_length by exact LEN;lia).
  cbn [Nat.sub firstn];rewrite app_nil_r.
  unfold wire_reserved_fields,wire_tail_valid;rewrite !wire_zero_bytes_app,!wire_word32_zero,!wire_word64_zero.
  rewrite !andb_assoc;reflexivity.
Qed.
Theorem wire_terminal_check : forall sequence r digest,
  length digest=32%nat -> zero_test(outgoing_frame sequence r digest)156 160=true.
Proof.
  intros sequence r digest LEN.
  change(zero_test(outgoing_frame sequence r digest)156(156+4)=true).
  rewrite wire_zero_span by(rewrite outgoing_frame_length by exact LEN;lia).
  rewrite wire_terminal_suffix by exact LEN;reflexivity.
Qed.
Theorem wire_digest_exact : forall sequence r digest,
  length digest=32%nat ->firstn 32(skipn 104(outgoing_frame sequence r digest))=digest.
Proof.
  intros sequence r digest LEN;unfold outgoing_frame;wire_skip_prefix.
  rewrite firstn_app,LEN,Nat.sub_diag,firstn_all2 by lia.
  cbn [firstn];apply app_nil_r.
Qed.
