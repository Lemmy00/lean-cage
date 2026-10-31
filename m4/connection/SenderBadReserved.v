(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.reporting: The actual reserved-byte mutation precedes all publication branches. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Slice IO Machine ClightSteps WriteAll StoreSteps LocalAccess Library LibraryMachine
  ResultLayout FrameRecord SenderSource SenderAccess SenderEncodingPrefix
  SenderStorage SenderOperations BytePatch SenderSelectors SenderGuards
  SenderGuardStages SenderReportMemory SenderReturn SenderWriteReturn
  SenderDuplicate ReportPaths.
Import ListNotations.
Open Scope Z_scope.
Definition sender_bad_tail := statement_drop 1 sender_reporting.
Definition selected_reserved_bytes fd r mode_bytes bytes :=
  if report_selected fd r mode_bytes bad_reserved then patch_bytes bytes 28 [Byte.repr 1] else bytes.
Lemma sender_bad_parts : sender_bad_tail=Ssequence (report_stage bad_reserved) sender_duplicate_tail.
Proof. reflexivity. Qed.
Theorem sender_bad_tail_source : forall allow_errors cell base m result_local bytes_local r digest bytes fd sequence
    mode mode_bytes locations le k,
  ~Mem.valid_block base result_local -> ~Mem.valid_block base bytes_local -> result_local<>bytes_local ->
  result_local<>tls_block cell -> bytes_local<>tls_block cell ->
  sender_storage base result_local bytes_local r digest bytes m ->
  sender_selectors cell base mode mode_bytes locations -> length bytes=160%nat -> call_cont k=Kstop ->
  le ! _fd=Some (Vint fd) -> le ! _sequence=Some (Vlong sequence) ->
  report_returns_allow allow_errors cell (sender_preserved cell base)
    (sender_return_result allow_errors base result_local bytes_local
      (selected_report_bytes fd r mode_bytes (selected_reserved_bytes fd r mode_bytes bytes)))
    (State f_send_frame sender_bad_tail k (sender_env result_local bytes_local) le m).
Proof.
  intros allow_errors cell base m result_local bytes_local r digest bytes fd sequence mode mode_bytes locations le k
    FR FB NE RNE BNE STORAGE SELECTORS LEN STOP FD SEQ.
  pose proof (old_sender_preserved cell _ _ (proj1 STORAGE)) as OLD.
  pose proof (sender_selectors_old _ _ _ _ _ _ (proj1 STORAGE) SELECTORS) as CURRENT.
  rewrite sender_bad_parts.
  eapply report_returns_source;[exact OLD|apply unchanged_store_edge;WriteAll.structural|].
  eapply sender_guard_stage;[exact OLD|exact (proj1 (proj2 STORAGE))|exact CURRENT|exact FD|exact SEQ|].
  intros next_le NEXTFD NEXTSEQ;unfold selected_reserved_bytes.
  destruct (report_selected fd r mode_bytes bad_reserved) eqn:BAD.
  - change (report_action bad_reserved) with (Sassign
      (Ederef (Ebinop Oadd (Evar _bytes (tarray tuchar 160)) (Econst_int (Int.repr 28) tint) (tptr tuchar)) tuchar)
      (Econst_int Int.one tint)).
    destruct (sender_byte_store base m result_local bytes_local r digest bytes 28%nat Int.one FB NE STORAGE LEN ltac:(lia))
      as [after [STORE NEXT]].
    eapply report_returns_source;[exact OLD| |].
    + eapply assignment_source_edge;[sender_location|sender_expression|reflexivity|].
      eapply assign_loc_value;[reflexivity|exact STORE].
    + change (sender_storage base result_local bytes_local r digest (patch_bytes bytes 28 [Byte.repr 1]) after) in NEXT.
      eapply report_returns_source;[apply old_sender_preserved;exact (proj1 NEXT)|apply unchanged_store_edge;WriteAll.structural|].
      eapply sender_duplicate_tail_source;[exact FR|exact FB|exact NE|exact RNE|exact BNE|
        apply sender_storage_live;exact NEXT|eapply sender_selectors_old;[exact (proj1 NEXT)|exact SELECTORS]|
        rewrite patch_bytes_length;[exact LEN|rewrite LEN;cbn;lia]|exact STOP|exact NEXTFD|exact NEXTSEQ].
  - eapply report_returns_source;[exact OLD|apply unchanged_store_edge;WriteAll.structural|].
    eapply sender_duplicate_tail_source;[exact FR|exact FB|exact NE|exact RNE|exact BNE|
      apply sender_storage_live;exact STORAGE|exact CURRENT|exact LEN|exact STOP|exact NEXTFD|exact NEXTSEQ].
Qed.
