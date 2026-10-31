(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-wire.fields: Finite initialized spans and exact zero-byte predicates. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers.
Require Import Readers FrameBytes DecoderValidity.
Import ListNotations.
Lemma wire_nth_seq_cons : forall (A : Type)(bytes : list A) b default start count,
  map(fun i=>nth i(b::bytes)default)(seq(S start)count)=
    map(fun i=>nth i bytes default)(seq start count).
Proof. intros A bytes b default start count;revert start;induction count;intros;cbn;[reflexivity|].
  f_equal;apply IHcount. Qed.
Lemma wire_nth_span : forall(A : Type)(bytes : list A)default start count,
  (start+count<=length bytes)%nat ->
  map(fun i=>nth i bytes default)(seq start count)=firstn count(skipn start bytes).
Proof.
  intros A bytes;induction bytes as[|b bytes IH];intros default start count BOUND.
  - assert(count=0)%nat by(cbn in BOUND;lia);subst count;reflexivity.
  - destruct start as[|start].
    + destruct count as[|count];[reflexivity|].
      cbn [seq map nth skipn firstn]. f_equal.
      change(map(fun i=>nth i(b::bytes)default)(seq(S 0)count)=firstn count bytes).
      rewrite wire_nth_seq_cons. apply(IH default 0%nat count);cbn in *;lia.
    + rewrite wire_nth_seq_cons. change(map(fun i=>nth i bytes default)(seq start count)=firstn count(skipn start bytes)).
      apply IH;cbn in *;lia.
Qed.
Lemma wire_forallb_map : forall(A B : Type)(f : B->bool)(g : A->B)xs,
  forallb f(map g xs)=forallb(fun x=>f(g x))xs.
Proof. intros A B f g xs;induction xs;cbn;[reflexivity|rewrite IHxs;reflexivity]. Qed.
Definition wire_zero_bytes bytes := forallb(fun b=>Int.eq(byte_word b)Int.zero)bytes.
Theorem wire_zero_span : forall bytes start count,
  (start+count<=length bytes)%nat ->
  zero_test bytes start(start+count)=wire_zero_bytes(firstn count(skipn start bytes)).
Proof.
  intros bytes start count BOUND. unfold zero_test,wire_zero_bytes.
  replace(start+count-start)%nat with count by lia.
  rewrite <- (wire_nth_span Byte.int bytes Byte.zero start count BOUND),wire_forallb_map.
  reflexivity.
Qed.
Lemma wire_zero_repeat : forall count,wire_zero_bytes(repeat Byte.zero count)=true.
Proof. induction count;cbn[wire_zero_bytes repeat forallb];[reflexivity|exact IHcount]. Qed.
