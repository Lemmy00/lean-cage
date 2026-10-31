(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.reporting: The deliberate short branch attempts exactly seventeen bytes. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Slice IO Machine ClightSteps WriteAll StoreSteps LocalAccess Library LibraryMachine
  ResultLayout FrameRecord SenderSource SenderAccess SenderEncodingPrefix
  SenderSelectors SenderGuards SenderGuardStages SenderReportMemory SenderReturn
  SenderWriteReturn SenderLastReport ReportPaths.
Import ListNotations.
Open Scope Z_scope.
Definition sender_short_tail := statement_drop 3 sender_reporting.
Definition selected_final_report fd r mode_bytes (bytes : list Byte.int) :=
  if report_selected fd r mode_bytes short_frame then firstn 17 bytes else
  if report_selected fd r mode_bytes drop_frame then [] else bytes.
Lemma sender_short_parts : sender_short_tail=Ssequence (report_stage short_frame) sender_drop_tail.
Proof. reflexivity. Qed.
Theorem sender_short_tail_source : forall allow_errors cell base m result_local bytes_local r digest bytes fd sequence
    mode mode_bytes locations le k,
  ~Mem.valid_block base result_local -> ~Mem.valid_block base bytes_local -> result_local<>bytes_local ->
  result_local<>tls_block cell -> bytes_local<>tls_block cell ->
  sender_live_memory cell base result_local bytes_local r digest bytes m ->
  sender_selectors cell m mode mode_bytes locations -> length bytes=160%nat -> call_cont k=Kstop ->
  le ! _fd=Some (Vint fd) -> le ! _sequence=Some (Vlong sequence) ->
  report_returns_allow allow_errors cell (sender_preserved cell base)
    (sender_return_result allow_errors base result_local bytes_local (selected_final_report fd r mode_bytes bytes))
    (State f_send_frame sender_short_tail k (sender_env result_local bytes_local) le m).
Proof.
  intros allow_errors cell base m result_local bytes_local r digest bytes fd sequence mode mode_bytes locations le k
    FR FB NE RNE BNE LIVE SELECTORS LEN STOP FD SEQ.
  rewrite sender_short_parts.
  eapply report_returns_source;[exact (proj1 LIVE)|apply unchanged_store_edge;WriteAll.structural|].
  eapply sender_guard_stage;[exact (proj1 LIVE)|exact (proj1 (proj2 LIVE))|exact SELECTORS|exact FD|exact SEQ|].
  intros next_le NEXTFD NEXTSEQ;unfold selected_final_report.
  destruct (report_selected fd r mode_bytes short_frame) eqn:SHORT.
  - change (report_action short_frame) with (Ssequence
      (Scall (Some _t'11) (Evar _write_all (Tfunction [tint;tptr tvoid;tulong] tint cc_default))
        [Etempvar _fd tint;Evar _bytes (tarray tuchar 160);Econst_int (Int.repr 17) tint])
      (Sreturn (Some (Etempvar _t'11 tint)))).
    eapply sender_write_return_source;[exact FR|exact FB|exact NE|exact RNE|exact BNE|exact LIVE|
      exact (proj1 SELECTORS)|exact LEN|lia|exact STOP|exact NEXTFD|sender_expression|reflexivity].
  - eapply report_returns_source;[exact (proj1 LIVE)|apply unchanged_store_edge;WriteAll.structural|].
    apply sender_drop_tail_source with (r:=r) (digest:=digest) (fd:=fd) (sequence:=sequence)
      (mode:=mode) (locations:=locations);assumption.
Qed.
