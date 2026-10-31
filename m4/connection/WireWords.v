(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-wire.fields: Recover actual emitted byte words without narrowing assumptions. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers.
Require Import Codec Readers Writers CodecRoundtrip FrameBytes FrameRecord.
Import ListNotations.
Open Scope Z_scope.
Lemma wire_byte_word : forall x,
  byte_word (Byte.repr (Int.unsigned x)) = Int.zero_ext 8 x.
Proof.
  intros x. unfold byte_word. rewrite Byte.unsigned_repr_eq.
  rewrite <- (Int.repr_unsigned (Int.zero_ext 8 x)).
  rewrite Int.zero_ext_mod by (change (0<=8<32);lia). reflexivity.
Qed.
Lemma wire_put32_byte : forall x i,
  byte_word (Byte.repr (Int.unsigned (put32_byte x i))) = put32_byte x i.
Proof. intros. rewrite wire_byte_word. unfold put32_byte. rewrite Int.zero_ext_idem by lia. reflexivity. Qed.
Lemma wire_put64_byte : forall x i,
  byte_word (Byte.repr (Int.unsigned (put64_byte x i))) = put64_byte x i.
Proof. intros. rewrite wire_byte_word. unfold put64_byte. rewrite Int.zero_ext_idem by lia. reflexivity. Qed.
Theorem wire_word32_head : forall x tail,
  word32_at (frame_word32 x ++ tail) 0 = x.
Proof.
  intros. unfold word32_at,byte_word_at,byte_at,frame_word32,put32_values.
  cbn [map app nth Nat.add]. rewrite !wire_put32_byte. apply put_get32_word.
Qed.
Theorem wire_word64_head : forall x tail,
  word64_at (frame_word64 x ++ tail) 0 = x.
Proof.
  intros. unfold word64_at,byte_word_at,byte_at,frame_word64,put64_values.
  cbn [map app nth Nat.add]. rewrite !wire_put64_byte. apply put_get64_word.
Qed.
Lemma wire_byte_skip : forall bytes start n,
  byte_word_at (skipn start bytes) n = byte_word_at bytes (start+n).
Proof.
  intros bytes start;revert bytes;induction start;intros bytes n.
  - rewrite Nat.add_0_l;reflexivity.
  - destruct bytes as[|b bytes];[destruct n;reflexivity|].
    change(byte_word_at(skipn start bytes)n=byte_word_at bytes(start+n));apply IHstart.
Qed.
Lemma wire_word32_skip : forall bytes start,
  word32_at bytes start = word32_at (skipn start bytes) 0.
Proof.
  intros. unfold word32_at. rewrite !wire_byte_skip. rewrite Nat.add_0_r. reflexivity.
Qed.
Lemma wire_word64_skip : forall bytes start,
  word64_at bytes start = word64_at (skipn start bytes) 0.
Proof.
  intros. unfold word64_at. rewrite !wire_byte_skip. rewrite Nat.add_0_r. reflexivity.
Qed.
Lemma wire_skip_past : forall (A : Type) (before after : list A) n,
  (length before<=n)%nat -> skipn n(before++after)=skipn(n-length before)after.
Proof. intros;rewrite skipn_app,skipn_all2 by assumption;reflexivity. Qed.
