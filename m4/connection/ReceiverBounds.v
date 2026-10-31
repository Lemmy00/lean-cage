(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-receiver.classification: A selected setup report has exact length and source stage/error bounds. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers.
Require Import FrameBytes ReceiverChoice ReceiverSelectionSource.
Open Scope Z_scope.
Theorem receiver_setup_bounds : forall bytes bad entered done status,
  (length bytes<=9)%nat -> rc_branch(receiver_select bytes bad entered done status)=choose_setup ->
  length bytes=8%nat /\ bad=Int.zero /\ entered=Int.zero /\
  1<=Int.unsigned(word32_at bytes 0)<=8 /\ 1<=Int.unsigned(word32_at bytes 4)<=4095.
Proof.
  intros bytes bad entered done status LIMIT SETUP.
  apply receiver_setup_exact in SETUP;unfold receiver_setup_guard in SETUP.
  repeat rewrite Bool.andb_true_iff in SETUP.
  destruct SETUP as[[[[[[BAD ENTERED]LEN]LOW]HIGH]POS]TOP].
  apply Bool.negb_true_iff in LOW;apply Bool.negb_true_iff in HIGH;apply Bool.negb_true_iff in TOP.
  apply Int.same_if_eq in BAD;apply Int.same_if_eq in ENTERED.
  split;[eapply receiver_eight_from_word;eassumption|]. split;[exact BAD|]. split;[exact ENTERED|].
  unfold Int.ltu in LOW,HIGH,POS,TOP.
  change(Int.unsigned Int.one)with 1 in LOW;change(Int.unsigned(Int.repr 8))with 8 in HIGH.
  change(Int.unsigned Int.zero)with 0 in POS;change(Int.unsigned(Int.repr 4095))with 4095 in TOP.
  destruct(zlt(Int.unsigned(word32_at bytes 0))1),
    (zlt 8(Int.unsigned(word32_at bytes 0))),
    (zlt 0(Int.unsigned(word32_at bytes 4))),
    (zlt 4095(Int.unsigned(word32_at bytes 4)));try discriminate;lia.
Qed.
Theorem receiver_setup_kind : forall bytes bad entered done status,
  rc_kind(receiver_select bytes bad entered done status)=Int.one ->
  rc_branch(receiver_select bytes bad entered done status)=choose_setup.
Proof.
  intros bytes bad entered done status;unfold receiver_select.
  destruct(receiver_setup_guard bytes bad entered),
    (receiver_wait_guard bytes bad entered done&&receiver_wait_exit status),
    (receiver_wait_guard bytes bad entered done&&receiver_wait_signal status);cbn;intros;try reflexivity;discriminate.
Qed.
Theorem receiver_bad_read_is_unknown : forall bytes entered done status,
  receiver_select bytes Int.one entered done status=
    {|rc_branch:=choose_unknown;rc_kind:=Int.repr 4;rc_stage:=Int.repr 9;rc_detail:=Int.repr 71;
      rc_entry:=if Int.eq entered Int.zero then Int.repr 2 else Int.one|}.
Proof. intros;reflexivity. Qed.
