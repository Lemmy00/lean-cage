(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.finish: Every branch after publication uses the copied result and frees it. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Slice IO Machine ClightSteps WriteAll StoreSteps LocalAccess CallAccess ResultLayout ScalarMemory
  FrameRecord SenderSource SenderReportMemory SenderReturn FinishSource SourcePaths DecoderControl.
Import ListNotations.
Open Scope Z_scope.
Definition finish_result base r value after := value=Vint (finish_exit_word r) /\
  exists local before,~Mem.valid_block base local /\ Mem.free before local 0 144=Some after.
Theorem finish_after_send_source : forall cell base m local le k r digest,
  ~Mem.valid_block base local -> sender_preserved cell base m ->
  frame_result_owned m local 0 r digest -> Mem.range_perm m local 0 144 Cur Freeable -> call_cont k=Kstop ->
  source_returns result_ge (sender_preserved cell base) (finish_result base r)
    (State f_finish finish_after_send k (finish_env local) le m).
Proof.
  intros cell base m local le k r digest FRESH OLD OWN FREEABLE STOP.
  destruct (Mem.range_perm_free _ _ _ _ FREEABLE) as [after FREE].
  assert (AFTER : sender_preserved cell base after) by (eapply sender_local_free_preserved;[exact FRESH|exact OLD|exact FREE]).
  let body:=eval cbv [finish_after_send finish_after_copy statement_drop fn_body f_finish] in finish_after_send in
    change (source_returns result_ge (sender_preserved cell base) (finish_result base r)
      (State f_finish body k (finish_env local) le m)).
  Ltac finish_controls r OWN OLD AFTER FREE STOP FRESH :=
    lazymatch goal with
    | |- source_returns _ _ _ (State _ (Sset _ (Efield _ _ _)) _ _ _ _) =>
      eapply source_returns_prepend;[exact OLD|eapply certified_set_edge;finish_field r OWN|];
      cbn [Val.load_result scalar_chunk scalar_value cell32];
      finish_controls r OWN OLD AFTER FREE STOP FRESH
    | |- source_returns _ _ _ (State _ (Sset _ _) _ _ _ _) =>
      eapply source_returns_prepend;[exact OLD|eapply certified_set_edge;finish_expression|];
      finish_controls r OWN OLD AFTER FREE STOP FRESH
    | |- source_returns _ _ _ (State _ (Sifthenelse _ _ _) _ _ _ _) =>
      eapply source_returns_prepend;[exact OLD|apply unchanged_store_edge;eapply edge_if;
        [decoder_control_expression|apply boolean_condition]|];
      cbn [Int.cmpu];
      lazymatch goal with |- source_returns _ _ _ (State _ (if ?test then _ else _) _ _ _ _) =>
        destruct test eqn:?;finish_controls r OWN OLD AFTER FREE STOP FRESH
      end
    | |- source_returns _ _ _ (State _ (Sreturn _) _ _ _ _) =>
      eapply source_returns_prepend;[exact OLD|eapply finish_source_return;
        [finish_expression|reflexivity|exact FREE]|];
      cbn [call_cont];rewrite ?STOP;
      apply source_returns_done;[exact AFTER|];
      split;[unfold finish_exit_word;cbn [cast_int_int] in *;change (Int.repr 0) with Int.zero in *;change (Int.repr 1) with Int.one in *;repeat match goal with H : Int.eq _ _ = _ |- _=>rewrite H end;reflexivity|
        eexists;eexists;split;[exact FRESH|exact FREE]]
    | |- source_returns _ _ _ (State _ _ _ _ _ _) =>
      eapply source_returns_prepend;[exact OLD|apply unchanged_store_edge;WriteAll.structural|];
      finish_controls r OWN OLD AFTER FREE STOP FRESH
    end.
  finish_controls r OWN OLD AFTER FREE STOP FRESH.
Qed.
