(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-wire.fields: Exact field constraints behind the private zero-tail check. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers.
Require Import Readers FrameBytes FrameRecord WireWords WireSpans.
Import ListNotations.
Open Scope Z_scope.
Lemma wire_bool_ext : forall a b : bool,(a=true <-> b=true)->a=b.
Proof. intros a b EQ;destruct a,b;intuition discriminate. Qed.
Lemma wire_byte_is_zero : forall b,Int.eq(byte_word b)Int.zero=true <-> b=Byte.zero.
Proof.
  intros b;split;[intros EQ|intros EQ;subst;reflexivity].
  apply Int.same_if_eq in EQ. apply(f_equal Int.unsigned)in EQ.
  unfold byte_word in EQ. rewrite Int.unsigned_repr in EQ by
    (pose proof(Byte.unsigned_range b);change(0<=Byte.unsigned b<=4294967295);change(0<=Byte.unsigned b<256)in H;lia).
  change(Byte.unsigned b=0)in EQ. rewrite <-(Byte.repr_unsigned b),EQ;reflexivity.
Qed.
Lemma wire_zero_bytes_exact : forall bytes,
  wire_zero_bytes bytes=true <-> bytes=repeat Byte.zero(length bytes).
Proof.
  induction bytes as[|b bytes IH];[cbn;tauto|].
  change(Int.eq(byte_word b)Int.zero && wire_zero_bytes bytes=true <->
    b::bytes=Byte.zero::repeat Byte.zero(length bytes)).
  rewrite andb_true_iff,wire_byte_is_zero,IH. split;intros EQ.
  - destruct EQ as[B E];f_equal;assumption.
  - injection EQ as B E;split;assumption.
Qed.
Theorem wire_word32_zero : forall x,
  wire_zero_bytes(frame_word32 x)=Int.eq x Int.zero.
Proof.
  intros x;apply wire_bool_ext;split.
  - intros ZERO;apply wire_zero_bytes_exact in ZERO;rewrite frame_word32_length in ZERO.
    pose proof(wire_word32_head x [])as READ;rewrite app_nil_r,ZERO in READ.
    change(Int.zero=x)in READ;subst;apply Int.eq_true.
  - intros EQ;apply Int.same_if_eq in EQ;subst;reflexivity.
Qed.
Theorem wire_word64_zero : forall x,
  wire_zero_bytes(frame_word64 x)=Int64.eq x Int64.zero.
Proof.
  intros x;apply wire_bool_ext;split.
  - intros ZERO;apply wire_zero_bytes_exact in ZERO;rewrite frame_word64_length in ZERO.
    pose proof(wire_word64_head x [])as READ;rewrite app_nil_r,ZERO in READ.
    change(Int64.zero=x)in READ;subst;apply Int64.eq_true.
  - intros EQ;apply Int64.same_if_eq in EQ;subst;reflexivity.
Qed.
Theorem wire_zero_bytes_app : forall a b,
  wire_zero_bytes(a++b)=wire_zero_bytes a && wire_zero_bytes b.
Proof. intros;unfold wire_zero_bytes;apply forallb_app. Qed.
