(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.reporting: Short and full source writes return their exact publication result. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Slice IO Machine ClightSteps WriteAll StoreSteps LocalAccess CallAccess Library LibraryMachine
  WriteMemory WriteCallers ResultLayout SenderSource SenderAccess SenderReportMemory SenderReturn
  SenderReportingSteps ProcessEffects WriteEffects ReportPaths.
Import ListNotations.
Open Scope Z_scope.
Definition sender_output_result (expected sent : list Byte.int) value :=
  (value=Vint Int.zero /\ sent=expected) \/
  (value=Vint Int.mone /\ sent<>expected /\ exists rest,expected=sent++rest).
Definition sender_return_result (allow_errors : bool) base result_local bytes_local expected sent value after :=
  sender_freed base result_local bytes_local after /\ sender_output_result expected sent value /\ (allow_errors=true \/ value=Vint Int.zero).

Theorem sender_write_return_source : forall allow_errors cell base m result_local bytes_local r digest bytes fd le k
    id count count_expr count_value,
  ~Mem.valid_block base result_local -> ~Mem.valid_block base bytes_local -> result_local<>bytes_local ->
  result_local<>tls_block cell -> bytes_local<>tls_block cell ->
  sender_live_memory cell base result_local bytes_local r digest bytes m -> tls_ready cell m ->
  length bytes=160%nat -> (count<=160)%nat -> call_cont k=Kstop ->
  le ! _fd=Some (Vint fd) ->
  expression_value result_ge (sender_env result_local bytes_local) le m count_expr count_value ->
  sem_cast count_value (typeof count_expr) tulong m=Some (Vlong (Int64.repr (Z.of_nat count))) ->
  report_returns_allow allow_errors cell (sender_preserved cell base)
    (sender_return_result allow_errors base result_local bytes_local (firstn count bytes))
    (State f_send_frame (Ssequence
      (Scall (Some id) (Evar _write_all (Tfunction [tint;tptr tvoid;tulong] tint cc_default))
        [Etempvar _fd tint;Evar _bytes (tarray tuchar 160);count_expr])
      (Sreturn (Some (Etempvar id tint)))) k (sender_env result_local bytes_local) le m).
Proof.
  intros allow_errors cell base m result_local bytes_local r digest bytes fd le k id count count_expr count_value
    FR FB NE RNE BNE LIVE TLS LEN BOUND STOP FD COUNT CAST.
  pose proof LIVE as [OLD [OWN [READ [RFREE BFREE]]]].
  pose proof (sender_frame_write_owned cell m fd bytes_local bytes count TLS BNE READ LEN BOUND) as INPUT.
  eapply report_returns_source;[exact OLD|apply unchanged_store_edge;WriteAll.structural|].
  eapply report_returns_source;[exact OLD|eapply sender_write_call_edge;[exact FD|exact COUNT|exact CAST]|].
  eapply report_returns_write.
  - apply sender_request_cell.
  - exact I.
  - discriminate.
  - exact OLD.
  - exact INPUT.
  - intros after HISTORY;eapply history_sender_preserved;[exact OLD|exact HISTORY].
  - intros events value after HISTORY [POST PREFIX] ALLOWED.
    pose proof (sender_live_history cell base m after result_local bytes_local r digest bytes RNE BNE LIVE HISTORY) as AFTER.
    eapply report_returns_source;[exact (proj1 AFTER)|apply unchanged_store_edge;WriteAll.structural|].
    eapply report_returns_source;[exact (proj1 AFTER)|apply unchanged_store_edge;WriteAll.structural|].
    destruct POST as [WOWN [[VALUE SENT]|[VALUE [FAILED SENT]]]];subst value.
    + eapply sender_return_certificate;[exact FR|exact FB|exact NE|exact AFTER|exact STOP|
        sender_expression|reflexivity|].
      intros final FREED;cbn;rewrite app_nil_r;split;[exact FREED|]. split;[left;auto|right;reflexivity].
    + eapply sender_return_certificate;[exact FR|exact FB|exact NE|exact AFTER|exact STOP|
        sender_expression|reflexivity|].
      intros final FREED;cbn;rewrite app_nil_r;split;[exact FREED|]. split;[right;auto|exact ALLOWED].
Qed.
