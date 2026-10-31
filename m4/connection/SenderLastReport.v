(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.reporting: Actual drop selection and final full-frame publication. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Slice IO Machine ClightSteps WriteAll StoreSteps LocalAccess Library LibraryMachine
  ResultLayout ProcessEffects FrameRecord SenderSource SenderAccess SenderEncodingPrefix
  SenderSelectors SenderGuards SenderGuardStages SenderReportMemory SenderReturn
  SenderReportingSteps SenderWriteReturn ReportPaths ReportConsequences.
Import ListNotations.
Open Scope Z_scope.
Definition sender_final_write := statement_drop 5 sender_reporting.
Definition sender_drop_tail := statement_drop 4 sender_reporting.
Lemma sender_drop_parts : sender_drop_tail=Ssequence (report_stage drop_frame) sender_final_write.
Proof. reflexivity. Qed.

Theorem sender_final_write_source : forall allow_errors cell base m result_local bytes_local r digest bytes fd le k,
  ~Mem.valid_block base result_local -> ~Mem.valid_block base bytes_local -> result_local<>bytes_local ->
  result_local<>tls_block cell -> bytes_local<>tls_block cell ->
  sender_live_memory cell base result_local bytes_local r digest bytes m -> tls_ready cell m ->
  length bytes=160%nat -> call_cont k=Kstop -> le ! _fd=Some (Vint fd) ->
  report_returns_allow allow_errors cell (sender_preserved cell base) (sender_return_result allow_errors base result_local bytes_local bytes)
    (State f_send_frame sender_final_write k (sender_env result_local bytes_local) le m).
Proof.
  intros allow_errors cell base m result_local bytes_local r digest bytes fd le k FR FB NE RNE BNE LIVE TLS LEN STOP FD.
  pose proof (sender_write_return_source allow_errors cell base m result_local bytes_local r digest bytes fd le k
    _t'18 160 (Esizeof (tarray tuchar 160) tulong) (Vlong (Int64.repr 160))
    FR FB NE RNE BNE LIVE TLS LEN ltac:(lia) STOP FD ltac:(apply sizeof_expression_value) eq_refl) as CERT.
  rewrite firstn_all2 in CERT by lia;exact CERT.
Qed.

Theorem sender_drop_tail_source : forall allow_errors cell base m result_local bytes_local r digest bytes fd sequence
    mode mode_bytes locations le k,
  ~Mem.valid_block base result_local -> ~Mem.valid_block base bytes_local -> result_local<>bytes_local ->
  result_local<>tls_block cell -> bytes_local<>tls_block cell ->
  sender_live_memory cell base result_local bytes_local r digest bytes m ->
  sender_selectors cell m mode mode_bytes locations -> length bytes=160%nat -> call_cont k=Kstop ->
  le ! _fd=Some (Vint fd) -> le ! _sequence=Some (Vlong sequence) ->
  report_returns_allow allow_errors cell (sender_preserved cell base)
    (sender_return_result allow_errors base result_local bytes_local
      (if report_selected fd r mode_bytes drop_frame then [] else bytes))
    (State f_send_frame sender_drop_tail k (sender_env result_local bytes_local) le m).
Proof.
  intros allow_errors cell base m result_local bytes_local r digest bytes fd sequence mode mode_bytes locations le k
    FR FB NE RNE BNE LIVE SELECTORS LEN STOP FD SEQ.
  rewrite sender_drop_parts.
  eapply report_returns_source;[exact (proj1 LIVE)|apply unchanged_store_edge;WriteAll.structural|].
  eapply sender_guard_stage;[exact (proj1 LIVE)|exact (proj1 (proj2 LIVE))|exact SELECTORS|exact FD|exact SEQ|].
  intros next_le NEXTFD NEXTSEQ;destruct (report_selected fd r mode_bytes drop_frame) eqn:DROP.
  - change (report_action drop_frame) with (Sreturn (Some (Econst_int Int.zero tint))).
    eapply sender_return_certificate;[exact FR|exact FB|exact NE|exact LIVE|exact STOP|sender_expression|reflexivity|].
    intros after FREED;split;[exact FREED|]. split;[left;auto|right;reflexivity].
  - eapply report_returns_source;[exact (proj1 LIVE)|apply unchanged_store_edge;WriteAll.structural|].
    apply sender_final_write_source with (r:=r) (digest:=digest) (fd:=fd);assumption || exact (proj1 SELECTORS).
Qed.
