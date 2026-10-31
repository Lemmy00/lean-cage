(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.reporting: Complete duplicate reporting preserves later selectors through I/O. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Slice IO Machine ClightSteps WriteAll StoreSteps LocalAccess Library LibraryMachine WriteMemory
  WriteCallers ResultLayout FrameRecord SenderSource SenderAccess SenderEncodingPrefix
  SenderSelectors SenderGuards SenderGuardStages SenderReportMemory SenderReturn
  SenderReportingSteps SenderWriteReturn SenderShortReport SenderOutcome
  ReportPaths ReportConsequences WriteEffects.
Import ListNotations.
Open Scope Z_scope.
Definition sender_duplicate_tail := statement_drop 2 sender_reporting.
Definition selected_report_bytes fd r mode_bytes bytes :=
  if report_selected fd r mode_bytes duplicate_frame then bytes++bytes else selected_final_report fd r mode_bytes bytes.
Lemma sender_duplicate_parts : sender_duplicate_tail=Ssequence (report_stage duplicate_frame) sender_short_tail.
Proof. reflexivity. Qed.
Theorem sender_duplicate_tail_source : forall allow_errors cell base m result_local bytes_local r digest bytes fd sequence
    mode mode_bytes locations le k,
  ~Mem.valid_block base result_local -> ~Mem.valid_block base bytes_local -> result_local<>bytes_local ->
  result_local<>tls_block cell -> bytes_local<>tls_block cell ->
  sender_live_memory cell base result_local bytes_local r digest bytes m ->
  sender_selectors cell m mode mode_bytes locations -> length bytes=160%nat -> call_cont k=Kstop ->
  le ! _fd=Some (Vint fd) -> le ! _sequence=Some (Vlong sequence) ->
  report_returns_allow allow_errors cell (sender_preserved cell base)
    (sender_return_result allow_errors base result_local bytes_local (selected_report_bytes fd r mode_bytes bytes))
    (State f_send_frame sender_duplicate_tail k (sender_env result_local bytes_local) le m).
Proof.
  intros allow_errors cell base m result_local bytes_local r digest bytes fd sequence mode mode_bytes locations le k
    FR FB NE RNE BNE LIVE SELECTORS LEN STOP FD SEQ.
  rewrite sender_duplicate_parts.
  eapply report_returns_source;[exact (proj1 LIVE)|apply unchanged_store_edge;WriteAll.structural|].
  eapply sender_guard_stage;[exact (proj1 LIVE)|exact (proj1 (proj2 LIVE))|exact SELECTORS|exact FD|exact SEQ|].
  intros next_le NEXTFD NEXTSEQ;unfold selected_report_bytes.
  destruct (report_selected fd r mode_bytes duplicate_frame) eqn:DUP.
  - change (report_action duplicate_frame) with (Ssequence
      (Scall (Some _t'7) (Evar _write_all (Tfunction [tint;tptr tvoid;tulong] tint cc_default))
        [Etempvar _fd tint;Evar _bytes (tarray tuchar 160);Esizeof (tarray tuchar 160) tulong])
      (Sifthenelse (Etempvar _t'7 tint) (Sreturn (Some (Eunop Oneg (Econst_int Int.one tint) tint))) Sskip)).
    eapply report_returns_source;[exact (proj1 LIVE)|apply unchanged_store_edge;WriteAll.structural|].
    eapply report_returns_source;[exact (proj1 LIVE)|eapply sender_write_call_edge with (count:=160%nat);
      [exact NEXTFD|apply sizeof_expression_value|reflexivity]|].
    assert (INPUT : write_owned (sender_request cell fd bytes_local 160%nat) bytes m).
    { pose proof (sender_frame_write_owned cell m fd bytes_local bytes 160%nat (proj1 SELECTORS) BNE
        (proj1 (proj2 (proj2 LIVE))) LEN ltac:(lia)) as OWN.
      rewrite firstn_all2 in OWN by lia;exact OWN. }
    eapply report_returns_write;[apply sender_request_cell|exact I|discriminate|exact (proj1 LIVE)|exact INPUT| |].
    + intros after HISTORY;eapply history_sender_preserved;[exact (proj1 LIVE)|exact HISTORY].
    + intros events value after HISTORY [POST PREFIX] ALLOWED.
      pose proof (sender_live_history cell base m after result_local bytes_local r digest bytes RNE BNE LIVE HISTORY) as AFTER.
      pose proof (sender_selectors_history _ _ _ _ _ _ HISTORY SELECTORS) as SELECTORS'.
      eapply report_returns_source;[exact (proj1 AFTER)|apply unchanged_store_edge;WriteAll.structural|].
      eapply report_returns_source;[exact (proj1 AFTER)|apply unchanged_store_edge;WriteAll.structural|].
      destruct POST as [WOWN [[VALUE SENT]|[VALUE [FAILED SENT]]]];subst value.
      * eapply report_returns_source;[exact (proj1 AFTER)|apply unchanged_store_edge;eapply edge_if;
          [eapply value_temp;WriteAll.lookup|reflexivity]|].
        eapply report_returns_source;[exact (proj1 AFTER)|apply unchanged_store_edge;WriteAll.structural|].
        eapply report_returns_consequence.
        -- eapply sender_short_tail_source;[exact FR|exact FB|exact NE|exact RNE|exact BNE|exact AFTER|exact SELECTORS'|
             exact LEN|exact STOP|WriteAll.lookup|WriteAll.lookup].
        -- intros more final last [FREED [RESULT ALLOWEDRESULT]];split;[exact FREED|]. split;[|exact ALLOWEDRESULT].
           rewrite (duplicate_final_report _ _ _ _ DUP) in RESULT.
           rewrite SENT;apply output_append_success;exact RESULT.
      * eapply report_returns_source;[exact (proj1 AFTER)|apply unchanged_store_edge;eapply edge_if;
          [eapply value_temp;WriteAll.lookup|reflexivity]|].
        eapply sender_return_certificate;[exact FR|exact FB|exact NE|exact AFTER|exact STOP|sender_expression|reflexivity|].
        intros final FREED;cbn;rewrite app_nil_r;split;[exact FREED|]. split;[apply output_failed_first;assumption|exact ALLOWED].
  - eapply report_returns_source;[exact (proj1 LIVE)|apply unchanged_store_edge;WriteAll.structural|].
    eapply sender_short_tail_source;[exact FR|exact FB|exact NE|exact RNE|exact BNE|exact LIVE|exact SELECTORS|
      exact LEN|exact STOP|exact NEXTFD|exact NEXTSEQ].
Qed.
