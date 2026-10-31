(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.reporting: The whole actual reporting suffix includes wrapped sequence mutation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Slice IO Machine ClightSteps WriteAll StoreSteps LocalAccess CallAccess Library LibraryMachine
  CallPaths FreshMemory ResultLayout FrameRecord SenderSource SenderAccess SenderEncodingPrefix
  SenderStorage SenderOperations BytePatch SenderSelectors SenderGuards
  SenderGuardStages SenderReportMemory SenderReturn SenderWriteReturn
  SenderDuplicate SenderBadReserved ReportPaths.
Import ListNotations.
Open Scope Z_scope.
Definition selected_sequence_bytes fd r mode_bytes sequence bytes :=
  if report_selected fd r mode_bytes wrong_sequence
  then patch_bytes bytes 16 (frame_word64 (Int64.add sequence Int64.one)) else bytes.
Definition selected_sender_bytes fd r mode_bytes sequence bytes :=
  selected_report_bytes fd r mode_bytes
    (selected_reserved_bytes fd r mode_bytes (selected_sequence_bytes fd r mode_bytes sequence bytes)).
Lemma sender_reporting_parts : sender_reporting=Ssequence (report_stage wrong_sequence) sender_bad_tail.
Proof. reflexivity. Qed.
Theorem sender_reporting_source : forall allow_errors cell base m result_local bytes_local r digest bytes fd sequence
    mode mode_bytes locations le k,
  ~Mem.valid_block base result_local -> ~Mem.valid_block base bytes_local -> result_local<>bytes_local ->
  result_local<>tls_block cell -> bytes_local<>tls_block cell ->
  sender_storage base result_local bytes_local r digest bytes m ->
  sender_selectors cell base mode mode_bytes locations -> length bytes=160%nat -> call_cont k=Kstop ->
  le ! _fd=Some (Vint fd) -> le ! _sequence=Some (Vlong sequence) ->
  report_returns_allow allow_errors cell (sender_preserved cell base)
    (sender_return_result allow_errors base result_local bytes_local (selected_sender_bytes fd r mode_bytes sequence bytes))
    (State f_send_frame sender_reporting k (sender_env result_local bytes_local) le m).
Proof.
  intros allow_errors cell base m result_local bytes_local r digest bytes fd sequence mode mode_bytes locations le k
    FR FB NE RNE BNE STORAGE SELECTORS LEN STOP FD SEQ.
  pose proof (old_sender_preserved cell _ _ (proj1 STORAGE)) as OLD.
  pose proof (sender_selectors_old _ _ _ _ _ _ (proj1 STORAGE) SELECTORS) as CURRENT.
  rewrite sender_reporting_parts.
  eapply report_returns_source;[exact OLD|apply unchanged_store_edge;WriteAll.structural|].
  eapply sender_guard_stage;[exact OLD|exact (proj1 (proj2 STORAGE))|exact CURRENT|exact FD|exact SEQ|].
  intros next_le NEXTFD NEXTSEQ;unfold selected_sender_bytes,selected_sequence_bytes.
  destruct (report_selected fd r mode_bytes wrong_sequence) eqn:WRONG.
  - change (report_action wrong_sequence) with (Scall None
      (Evar _put64 (Tfunction [tptr tuchar;tulong] tvoid cc_default))
      [Ebinop Oadd (Evar _bytes (tarray tuchar 160)) (Econst_int (Int.repr 16) tint) (tptr tuchar);
       Ebinop Oadd (Etempvar _sequence tulong) (Econst_int Int.one tint) tulong]).
    destruct sender_encoding_symbols as [b32 [b64 [bc [S32 [F32 [S64 [F64 [CS CF]]]]]]]].
    eapply report_returns_source;[exact OLD| |].
    + eapply certified_call_edge;[reflexivity|apply old_expression_value;eapply value_function;
        [unfold sender_env;cbn;reflexivity|exact S64|reflexivity]|sender_arguments|exact F64|reflexivity].
    + lazymatch goal with |- report_returns_allow _ _ _ _ (Callstate _ _ ?call _) =>
        destruct (sender_writer64 base m result_local bytes_local r digest bytes 16%nat
          (Int64.add sequence Int64.one) call FB NE STORAGE LEN ltac:(lia) I)
          as [after [PATH NEXT]]
      end.
      eapply report_returns_path;[eapply store_path_consequence;[exact PATH|intros;apply old_sender_preserved;assumption]|].
      eapply report_returns_source;[apply old_sender_preserved;exact (proj1 NEXT)|apply unchanged_store_edge;WriteAll.structural|].
      eapply report_returns_source;[apply old_sender_preserved;exact (proj1 NEXT)|apply unchanged_store_edge;WriteAll.structural|].
      eapply sender_bad_tail_source;[exact FR|exact FB|exact NE|exact RNE|exact BNE|exact NEXT|exact SELECTORS|
        rewrite patch_bytes_length;[exact LEN|rewrite LEN;cbn [frame_word64 Writers.put64_values map length];lia]|
        exact STOP|WriteAll.lookup|WriteAll.lookup].
  - eapply report_returns_source;[exact OLD|apply unchanged_store_edge;WriteAll.structural|].
    eapply sender_bad_tail_source;[exact FR|exact FB|exact NE|exact RNE|exact BNE|exact STORAGE|exact SELECTORS|
      exact LEN|exact STOP|exact NEXTFD|exact NEXTSEQ].
Qed.
