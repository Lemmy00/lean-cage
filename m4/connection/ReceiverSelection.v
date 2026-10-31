(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-receiver.classification: All actual terminal-classifier branches reach the exact result constructor. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Slice Machine ClightSteps StoreSteps WriteAll LocalAccess CallAccess CallPaths Library Readers
  ResultLayout ResultSource FrameBytes SourceReach DecoderControl SenderSource ReceiverSource ReceiverReadSource
  ReceiverChoice ReceiverSelectionSource.
Import ListNotations.
Open Scope Z_scope.

Theorem receiver_selection_source : forall (cell : tls) b bytes bad entered done status le k m,
  readable_bytes m{|address_block:=rb_bytes b;address_offset:=0|}bytes -> (length bytes<=9)%nat ->
  le!_bad=Some(Vint bad) -> le!_entered=Some(Vint entered) ->
  le!_leader_done=Some(Vint done) -> le!_leader_status=Some(Vint status) ->
  le!_used=Some(Vlong(Int64.repr(Z.of_nat(length bytes)))) ->
  source_reaches result_ge(fun after=>after=m)
    (receiver_selection_boundary b(receiver_select bytes bad entered done status)le k m)
    (State f_m4_collect_failure receiver_classify(Kseq receiver_copy_return k)(receiver_env b)le m).
Proof.
  intros cell b bytes bad entered done status le k m READ LIMIT BAD ENTERED DONE STATUS USED.
  destruct receiver_reader_symbol as[reader[RS RF]].
  destruct receiver_result_symbol as[result[CS CF]].
  unfold receiver_classify,receiver_after_close,receiver_after_loop;cbn [statement_drop first_statement].
  Ltac selection_normalize :=
    unfold Int.one,Int.zero,Int64.zero in *;
    cbn [cast_int_int Int.cmp Int.cmpu Int64.cmp Int64.cmpu]in *;
    change (cast_int_long Signed (Int.repr 8)) with (Int64.repr 8) in *;
    change (cast_int_long Signed (Int.repr 0)) with (Int64.repr 0) in *;
    repeat rewrite Int.eq_true in *;
    repeat rewrite Int64.eq_true in *;
    repeat rewrite Bool.negb_involutive in *;
    repeat rewrite cast_bool_zero_test in *;
    repeat rewrite bool_value_zero_test in *;
    repeat match goal with
      | H : negb _=true |- _=>apply Bool.negb_true_iff in H
      | H : negb _=false |- _=>apply Bool.negb_false_iff in H
    end.
  Ltac selection_truth :=
    unfold receiver_select,receiver_setup_guard,receiver_wait_guard,receiver_wait_exit,
      receiver_wait_signal,receiver_exit_detail,receiver_signal_detail;
    selection_normalize;
    repeat match goal with
      | H : ?a=true |- _=>progress rewrite H
      | H : ?a=false |- _=>progress rewrite H
    end;
    cbn [rc_branch rc_kind rc_stage rc_detail rc_entry receiver_choice_block receiver_choice_ident];reflexivity.
  Ltac selection_done :=
    apply source_reaches_done;[reflexivity|];unfold receiver_selection_boundary;eexists;split;
    [unfold receiver_choice_call,receiver_choice_cont,receiver_choice_copy,result_args;selection_truth|
      receiver_keep].
  Ltac selection_reader cell b bytes m READ LIMIT RS RF n :=
    let EIGHT:=fresh "EIGHT" in
    assert(EIGHT : length bytes=8%nat)by
      (apply receiver_eight_from_word;[exact LIMIT|selection_normalize;assumption]);
    receiver_choice_source_call RS RF;
    eapply source_reaches_path;
    [eapply(reader_caller_path result_ge cell);
      [exact(frame_reader32_input m {|address_block:=rb_bytes b;address_offset:=0|} bytes n READ ltac:(rewrite EIGHT;lia))|
       reflexivity]|].
  Ltac selection_run cell b bytes m READ LIMIT RS RF CS CF :=
    try solve [selection_normalize;congruence];
    try match goal with H : true=false |- _=>discriminate H
      |H : false=true |- _=>discriminate H end;
    cbn [call_cont];
    lazymatch goal with
    | |- source_reaches _ _ _ (Callstate(Internal f_result_of)_ _ _)=>selection_done
    | |- source_reaches _ _ _ (State _ (Scall _ (Evar _get32 _) [Evar _failure_bytes _]) _ _ _ _)=>
        selection_reader cell b bytes m READ LIMIT RS RF 0%nat;selection_run cell b bytes m READ LIMIT RS RF CS CF
    | |- source_reaches _ _ _ (State _ (Scall _ (Evar _get32 _) [Ebinop Oadd _ _ _]) _ _ _ _)=>
        selection_reader cell b bytes m READ LIMIT RS RF 4%nat;selection_run cell b bytes m READ LIMIT RS RF CS CF
    | |- source_reaches _ _ _ (State _ (Scall _ (Evar _result_of _) _) _ _ _ _)=>
        receiver_choice_source_call CS CF;selection_run cell b bytes m READ LIMIT RS RF CS CF
    | _=>first
      [receiver_choice_route|receiver_choice_set|
       receiver_choice_if;
        try lazymatch goal with |- source_reaches _ _ _ (State _ (if ?test then _ else _) _ _ _ _)=>
          let CHOICE:=fresh "CHOICE" in destruct test eqn:CHOICE end
       |fail 100 "No receiver selection source step"];
      selection_run cell b bytes m READ LIMIT RS RF CS CF
    end.
  selection_run cell b bytes m READ LIMIT RS RF CS CF.
Qed.
