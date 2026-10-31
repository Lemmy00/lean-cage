(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-receiver.classification: Exact raw terminal classification; wait-status provenance remains external. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Ctypesdefs Clight.
Require Import Slice FrameBytes FrameRecord ReceiverSource.
Import ListNotations.
Open Scope Z_scope.

Inductive receiver_branch := choose_setup | choose_exit | choose_signal | choose_unknown.
Record receiver_choice := {
  rc_branch : receiver_branch; rc_kind : int; rc_stage : int; rc_detail : int; rc_entry : int
}.
Definition receiver_setup_guard bytes bad entered :=
  Int.eq bad Int.zero && Int.eq entered Int.zero &&
  Int64.eq(Int64.repr(Z.of_nat(length bytes)))(Int64.repr 8) &&
  negb(Int.ltu(word32_at bytes 0)Int.one) &&
  negb(Int.ltu(Int.repr 8)(word32_at bytes 0)) &&
  Int.ltu Int.zero(word32_at bytes 4) &&
  negb(Int.ltu(Int.repr 4095)(word32_at bytes 4)).
Definition receiver_wait_guard (bytes : list Byte.int) bad entered done :=
  Int.eq bad Int.zero && negb(Int.eq entered Int.zero) &&
  Int64.eq(Int64.repr(Z.of_nat(length bytes)))Int64.zero && negb(Int.eq done Int.zero).
Definition receiver_wait_exit status := Int.eq(Int.and status(Int.repr 127))Int.zero.
Definition receiver_wait_signal status :=
  Int.lt Int.zero(Int.shr(Int.sign_ext 8(Int.add(Int.and status(Int.repr 127))Int.one))Int.one).
Definition receiver_exit_detail status := Int.shr(Int.and status(Int.repr 65280))(Int.repr 8).
Definition receiver_signal_detail status := Int.and status(Int.repr 127).
Definition receiver_select bytes bad entered done status :=
  if receiver_setup_guard bytes bad entered then
    {|rc_branch:=choose_setup;rc_kind:=Int.one;rc_stage:=word32_at bytes 0;
      rc_detail:=word32_at bytes 4;rc_entry:=Int.zero|}
  else if receiver_wait_guard bytes bad entered done && receiver_wait_exit status then
    {|rc_branch:=choose_exit;rc_kind:=Int.zero;rc_stage:=Int.zero;
      rc_detail:=receiver_exit_detail status;rc_entry:=Int.one|}
  else if receiver_wait_guard bytes bad entered done && receiver_wait_signal status then
    {|rc_branch:=choose_signal;rc_kind:=Int.repr 2;rc_stage:=Int.zero;
      rc_detail:=receiver_signal_detail status;rc_entry:=Int.one|}
  else {|rc_branch:=choose_unknown;rc_kind:=Int.repr 4;rc_stage:=Int.repr 9;
    rc_detail:=Int.repr 71;rc_entry:=if Int.eq entered Int.zero then Int.repr 2 else Int.one|}.

Definition receiver_choice_block b choice := match rc_branch choice with
  |choose_setup=>rb_setup b|choose_exit=>rb_exit b|choose_signal=>rb_signal b|choose_unknown=>rb_unknown b end.
Definition receiver_choice_ident choice := match rc_branch choice with
  |choose_setup=>__res__4|choose_exit=>__res__3|choose_signal=>__res__2|choose_unknown=>__res__1 end.

Theorem receiver_setup_exact : forall bytes bad entered done status,
  rc_branch(receiver_select bytes bad entered done status)=choose_setup <->
    receiver_setup_guard bytes bad entered=true.
Proof.
  intros;unfold receiver_select;destruct(receiver_setup_guard bytes bad entered);[cbn;tauto|].
  destruct(receiver_wait_guard bytes bad entered done && receiver_wait_exit status),
    (receiver_wait_guard bytes bad entered done && receiver_wait_signal status);cbn;split;discriminate.
Qed.

Theorem receiver_selected_kinds : forall bytes bad entered done status,
  In(rc_kind(receiver_select bytes bad entered done status))[Int.zero;Int.one;Int.repr 2;Int.repr 4].
Proof.
  intros;unfold receiver_select;destruct(receiver_setup_guard bytes bad entered),
    (receiver_wait_guard bytes bad entered done && receiver_wait_exit status),
    (receiver_wait_guard bytes bad entered done && receiver_wait_signal status);cbn;tauto.
Qed.

Example receiver_short_is_unknown :
  rc_branch(receiver_select(repeat Byte.zero 3)Int.zero Int.zero Int.one Int.zero)=choose_unknown.
Proof. vm_compute;reflexivity. Qed.
Example receiver_ninth_byte_is_unknown :
  rc_branch(receiver_select(frame_word32 Int.one++frame_word32 Int.one++[Byte.zero])
    Int.zero Int.zero Int.one Int.zero)=choose_unknown.
Proof. vm_compute;reflexivity. Qed.
Example receiver_setup_sample :
  receiver_select(frame_word32 Int.one++frame_word32(Int.repr 13))Int.zero Int.zero Int.one Int.zero=
    {|rc_branch:=choose_setup;rc_kind:=Int.one;rc_stage:=Int.one;rc_detail:=Int.repr 13;rc_entry:=Int.zero|}.
Proof. vm_compute;reflexivity. Qed.
Example receiver_arbitrary_status_is_not_a_signal_domain_proof :
  receiver_select[]Int.zero Int.one Int.one(Int.repr 65)=
    {|rc_branch:=choose_signal;rc_kind:=Int.repr 2;rc_stage:=Int.zero;rc_detail:=Int.repr 65;rc_entry:=Int.one|}.
Proof. vm_compute;reflexivity. Qed.
