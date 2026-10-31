(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-decoder.source: Byte-level validity linked to actual comparison and zero-loop outcomes. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers Values Memory.
Require Import Library FrameBytes DecoderHeader DecoderCommon DecoderTags DecoderZeros.
Import ListNotations.
Open Scope Z_scope.
Definition frame_magic := [Byte.repr 76;Byte.repr 67;Byte.repr 51;Byte.repr 82].
Definition magic_matches bytes :=
  match compare_bytes (firstn 4 bytes) frame_magic with Eq => true | _ => false end.
Definition zero_test bytes low high :=
  forallb (fun i => Int.eq (byte_word_at bytes i) Int.zero) (seq low (high-low)).
Definition header_prefix bytes run sequence :=
  magic_matches bytes && Int.eq (byte_word_at bytes 4) (Int.repr 1) &&
  Int.eq (byte_word_at bytes 5) Int.zero && Int.eq (byte_word_at bytes 7) Int.zero &&
  Int64.eq (word64_at bytes 8) run && Int64.eq (word64_at bytes 16) sequence &&
  Int.eq (word32_at bytes 24) (Int.repr 128) && Int.eq (word32_at bytes 28) Int.zero.
Definition header_valid bytes run sequence := header_prefix bytes run sequence && zero_test bytes 156 160.
Definition decoder_accepts bytes run uid preflight sequence :=
  header_valid bytes run sequence && common_valid bytes uid && zero_test bytes 96 156 && tag_valid bytes preflight.

Theorem zero_test_true : forall bytes low high,
  (low <= high)%nat -> (zero_test bytes low high = true <-> zero_range bytes low high).
Proof.
  intros bytes low high BOUND. unfold zero_test, zero_range. rewrite forallb_forall.
  split; intros H i RANGE.
  - apply Int.same_if_eq. apply H. apply in_seq; lia.
  - apply in_seq in RANGE. rewrite H by lia. apply Int.eq_true.
Qed.
Theorem zero_test_rejects : forall bytes low high i,
  (low <= i < high)%nat -> byte_word_at bytes i <> Int.zero -> zero_test bytes low high = false.
Proof.
  intros bytes low high i RANGE NE. destruct (zero_test bytes low high) eqn:TEST; [|reflexivity].
  exfalso; apply NE. apply (proj1 (zero_test_true bytes low high ltac:(lia)) TEST); exact RANGE.
Qed.
Lemma frame_prefix_owned : forall m p bytes,
  readable_bytes m p bytes -> length bytes = 160%nat -> readable_bytes m p (firstn 4 bytes).
Proof.
  intros m p bytes READ LEN.
  pose proof (readable_subspan m p bytes 0 4 READ ltac:(rewrite LEN;lia) ltac:(rewrite LEN;lia)) as PREFIX.
  cbn [skipn] in PREFIX.
  replace (offset_address p 0) with p in PREFIX; [exact PREFIX|].
  destruct p; unfold offset_address; cbn; rewrite Z.add_0_r; reflexivity.
Qed.
Theorem frame_comparison_zero : forall m p magic bytes value,
  readable_bytes m p bytes -> length bytes = 160%nat -> readable_bytes m magic frame_magic ->
  memcmp_result m p magic 4 value -> Int.eq value Int.zero = magic_matches bytes.
Proof.
  intros m p magic bytes value READ LEN MAGIC [xs [ys [X [Y [SIZE [LENGTH RESULT]]]]]].
  assert (XS : xs=firstn 4 bytes).
  { eapply readable_bytes_unique; [exact X|apply frame_prefix_owned; eassumption|].
    rewrite firstn_length,LEN; cbn; lia. }
  assert (YS : ys=frame_magic).
  { eapply readable_bytes_unique; [exact Y|exact MAGIC|]. unfold frame_magic; cbn;lia. }
  subst. apply comparison_result_zero; exact RESULT.
Qed.
Theorem header_comparison_exact : forall m p magic bytes value run sequence,
  readable_bytes m p bytes -> length bytes=160%nat -> readable_bytes m magic frame_magic ->
  memcmp_result m p magic 4 value -> header_matches value bytes run sequence = header_prefix bytes run sequence.
Proof.
  intros. unfold header_matches,header_prefix.
  rewrite (frame_comparison_zero m p magic bytes value H H0 H1 H2); reflexivity.
Qed.
