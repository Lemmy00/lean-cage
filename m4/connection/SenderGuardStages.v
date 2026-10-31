(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.reporting: Branch on the value returned by each actual source selector guard. *)
From Coq Require Import ZArith List.
From compcert Require Import Maps Integers AST Values Memory Clight.
Require Import Slice Machine ClightSteps WriteAll StoreSteps Library LocalAccess ResultLayout
  FrameRecord SenderSource SenderSelectors SenderGuards DecoderControl ReportPaths.
Open Scope Z_scope.
Theorem sender_guard_stage : forall allow_errors cell (P : mem -> Prop) R m result_local bytes_local r digest
    fd sequence mode mode_bytes locations tag le k,
  P m -> frame_result_owned m result_local 0 r digest ->
  sender_selectors cell m mode mode_bytes locations ->
  le ! _fd=Some (Vint fd) -> le ! _sequence=Some (Vlong sequence) ->
  (forall next_le,next_le ! _fd=Some (Vint fd) -> next_le ! _sequence=Some (Vlong sequence) ->
    report_returns_allow allow_errors cell P R (State f_send_frame
      (if report_selected fd r mode_bytes tag then report_action tag else Sskip)
      k (sender_env result_local bytes_local) next_le m)) ->
  report_returns_allow allow_errors cell P R (State f_send_frame (report_stage tag) k (sender_env result_local bytes_local) le m).
Proof.
  intros allow_errors cell P R m result_local bytes_local r digest fd sequence mode mode_bytes locations tag le k
    PM OWN SELECTORS FD SEQ NEXT.
  rewrite report_stage_source.
  eapply report_returns_source;[exact PM|apply unchanged_store_edge;WriteAll.structural|].
  eapply sender_guard_source;[exact PM|exact OWN|exact SELECTORS|exact FD|exact SEQ|].
  intros next_le NEXTFD NEXTSEQ FLAG.
  eapply report_returns_source;[exact PM|apply unchanged_store_edge;eapply edge_if;
    [eapply value_temp;exact FLAG|apply boolean_condition]|].
  apply NEXT;assumption.
Qed.
