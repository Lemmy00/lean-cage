(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.reporting: Exact zero-return byte counts retain all deliberate publication modes. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers Values Memory Clight.
Require Import Machine LibraryMachine ResultLayout ReportingTrace FrameRecord BytePatch SenderSelectors
  SenderShortReport SenderDuplicate SenderBadReserved SenderReporting SenderSource
  SenderProgram SenderWriteReturn.
Import ListNotations.
Open Scope Z_scope.
Theorem sender_expected_length : forall fd sequence r digest mode_bytes,
  length digest=32%nat -> length (sender_expected fd sequence r digest mode_bytes)=
    (if report_selected fd r mode_bytes duplicate_frame then 320 else
     if report_selected fd r mode_bytes short_frame then 17 else
     if report_selected fd r mode_bytes drop_frame then 0 else 160)%nat.
Proof.
  intros fd sequence r digest mode_bytes LEN.
  assert (FIRST : length (selected_sequence_bytes fd r mode_bytes sequence (outgoing_frame sequence r digest))=160%nat).
  { unfold selected_sequence_bytes;destruct (report_selected fd r mode_bytes wrong_sequence);
      [rewrite patch_bytes_length;[apply outgoing_frame_length;exact LEN|rewrite outgoing_frame_length,frame_word64_length;auto;lia]|
       apply outgoing_frame_length;exact LEN]. }
  assert (SECOND : length (selected_reserved_bytes fd r mode_bytes
    (selected_sequence_bytes fd r mode_bytes sequence (outgoing_frame sequence r digest)))=160%nat).
  { unfold selected_reserved_bytes;destruct (report_selected fd r mode_bytes bad_reserved);
      [rewrite patch_bytes_length;[exact FIRST|rewrite FIRST;cbn;lia]|exact FIRST]. }
  unfold sender_expected,selected_sender_bytes,selected_report_bytes,selected_final_report.
  destruct (report_selected fd r mode_bytes duplicate_frame);[rewrite app_length,SECOND;reflexivity|].
  destruct (report_selected fd r mode_bytes short_frame);[rewrite firstn_length,SECOND;reflexivity|].
  destruct (report_selected fd r mode_bytes drop_frame);[reflexivity|exact SECOND].
Qed.
Theorem standard_descriptor_frame : forall sequence r digest mode_bytes,
  sender_expected Int.one sequence r digest mode_bytes=outgoing_frame sequence r digest.
Proof. intros;unfold sender_expected,selected_sender_bytes,selected_report_bytes,selected_final_report,
  selected_reserved_bytes,selected_sequence_bytes,report_selected,report_enabled;reflexivity. Qed.
Theorem disabled_selector_frame : forall fd sequence r digest mode_bytes,
  report_enabled fd r=false -> sender_expected fd sequence r digest mode_bytes=outgoing_frame sequence r digest.
Proof. intros;unfold sender_expected,selected_sender_bytes,selected_report_bytes,selected_final_report,
  selected_reserved_bytes,selected_sequence_bytes,report_selected;rewrite H;reflexivity. Qed.
Theorem sender_zero_return_counts : forall cell base fd sequence input ofs r digest mode mode_bytes locations events after,
  sender_input cell base input ofs r digest mode mode_bytes locations ->
  library_steps result_ge cell (live (sender_initial fd sequence input ofs Kstop base)) events
    (live (Returnstate (Vint Int.zero) Kstop after)) ->
  In (length (reporting_trace events)) [0%nat;17%nat;160%nat;320%nat].
Proof.
  intros cell base fd sequence input ofs r digest mode mode_bytes locations events after INPUT RUN.
  destruct (sender_all_returns _ _ _ _ _ _ _ _ _ _ _ _ _ _ INPUT RUN) as [_ [[VALUE BYTES]|[VALUE FAILED]]];[|discriminate].
  rewrite BYTES,sender_expected_length.
  - destruct (report_selected fd r mode_bytes duplicate_frame), (report_selected fd r mode_bytes short_frame),
      (report_selected fd r mode_bytes drop_frame);cbn;tauto.
  - exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj1 INPUT)))))).
Qed.
Theorem sender_prefix_byte_bound : forall cell base fd sequence input ofs r digest mode mode_bytes locations events target,
  sender_input cell base input ofs r digest mode mode_bytes locations ->
  library_steps result_ge cell (live (sender_initial fd sequence input ofs Kstop base)) events target ->
  (length (reporting_trace events)<=320)%nat.
Proof.
  intros cell base fd sequence input ofs r digest mode mode_bytes locations events target INPUT RUN.
  destruct (sender_all_prefixes _ _ _ _ _ _ _ _ _ _ _ _ _ INPUT RUN) as [_ [rest PREFIX]].
  pose proof (f_equal (@length Byte.int) PREFIX) as LEN.
  rewrite app_length,sender_expected_length in LEN.
  - destruct (report_selected fd r mode_bytes duplicate_frame), (report_selected fd r mode_bytes short_frame),
      (report_selected fd r mode_bytes drop_frame);cbn in LEN;lia.
  - exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj1 INPUT)))))).
Qed.
