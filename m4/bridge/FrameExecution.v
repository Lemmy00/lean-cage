(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-bridge.frames: Exact imported frame operations and source observations. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers Values Memory Clight.
From LeanImport Require Import Lean.
Require Import NormalizedImport BridgeBytes Machine LibraryMachine LibraryWitnesses ResultLayout ReportingTrace
 FrameRecord SenderSelectors SenderGlobals SenderWitnesses SenderSource SenderProgram
 SenderSuccessfulRuns SenderOutcomes SenderWriteReturn
 FrameDecode FrameComplete FrameLengths.
Local Close Scope lean_scope.
Local Open Scope Z_scope.
Import ListNotations.

Lemma sender_digest_length cell base input ofs r digest mode mode_bytes locations :
 sender_input cell base input ofs r digest mode mode_bytes locations -> length digest=32%nat.
Proof. intro INPUT; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj1 INPUT)))))). Qed.
Theorem source_sender_imported_success
 cell base fd sequence input ofs r digest mode mode_bytes locations events after :
 sender_input cell base input ofs r digest mode mode_bytes locations ->
 library_steps result_ge cell (live (sender_initial fd sequence input ofs Kstop base)) events
   (live (Returnstate (Vint Int.zero) Kstop after)) ->
 LeanCageM4_Normalized_decode (imported_bytes (reporting_trace events)) =
 LeanCageM4_Normalized_decode (imported_bytes (sender_expected fd sequence r digest mode_bytes)).
Proof.
 intros INPUT RUN.
 destruct (sender_all_returns _ _ _ _ _ _ _ _ _ _ _ _ _ _ INPUT RUN)
   as [_ [[VALUE BYTES]|[VALUE FAILED]]]; [now rewrite BYTES|discriminate].
Qed.
Theorem source_sender_imported_frame
 cell base fd sequence input ofs r digest mode mode_bytes locations events after :
 sender_input cell base input ofs r digest mode mode_bytes locations ->
 report_enabled fd r=false ->
 library_steps result_ge cell (live (sender_initial fd sequence input ofs Kstop base)) events
   (live (Returnstate (Vint Int.zero) Kstop after)) ->
 LeanCageM4_Normalized_decode (imported_bytes (reporting_trace events)) =
 source_complete_decode sequence r digest.
Proof.
 intros INPUT DISABLED RUN.
 rewrite (source_sender_imported_success _ _ _ _ _ _ _ _ _ _ _ _ _ INPUT RUN).
 rewrite disabled_selector_frame by exact DISABLED.
 apply imported_complete_frame; eapply sender_digest_length; exact INPUT.
Qed.
Theorem source_sender_wrong_length_rejected
 cell base fd sequence input ofs r digest mode mode_bytes locations events after :
 sender_input cell base input ofs r digest mode mode_bytes locations ->
 library_steps result_ge cell (live (sender_initial fd sequence input ofs Kstop base)) events
   (live (Returnstate (Vint Int.zero) Kstop after)) ->
 length (sender_expected fd sequence r digest mode_bytes) <> 160%nat ->
 LeanCageM4_Normalized_decode (imported_bytes (reporting_trace events)) =
 Except_error_inst3 LeanCageM4_Normalized_ErrorCode LeanCageM3_Result LeanCageM4_Normalized_ErrorCode_header.
Proof.
 intros INPUT RUN LEN; rewrite (source_sender_imported_success _ _ _ _ _ _ _ _ _ _ _ _ _ INPUT RUN).
 apply imported_bad_length_rejected; exact LEN.
Qed.
Theorem source_sender_prefix_connection
 cell base fd sequence input ofs r digest mode mode_bytes locations events target :
 sender_input cell base input ofs r digest mode mode_bytes locations ->
 library_steps result_ge cell (live (sender_initial fd sequence input ofs Kstop base)) events target ->
 (exists rest, sender_expected fd sequence r digest mode_bytes=reporting_trace events++rest) /\
 (length (reporting_trace events) <> 160%nat ->
   LeanCageM4_Normalized_decode (imported_bytes (reporting_trace events)) =
   Except_error_inst3 LeanCageM4_Normalized_ErrorCode LeanCageM3_Result LeanCageM4_Normalized_ErrorCode_header).
Proof.
 intros INPUT RUN; split.
 - exact (proj2 (sender_all_prefixes _ _ _ _ _ _ _ _ _ _ _ _ _ INPUT RUN)).
 - apply imported_bad_length_rejected.
Qed.
Theorem source_sender_imported_nonvacuous r digest sequence :
 length digest=32%nat -> exists cell base input mode events after,
 sender_input cell base input 0 r digest mode normal_bytes sender_literal_location /\
 library_steps result_ge cell (live (sender_initial Int.one sequence input 0 Kstop base)) events
   (live (Returnstate (Vint Int.zero) Kstop after)) /\
 reporting_trace events=outgoing_frame sequence r digest /\
 LeanCageM4_Normalized_decode (imported_bytes (reporting_trace events)) = source_complete_decode sequence r digest.
Proof.
 intro LEN.
 destruct (arbitrary_sender_input r digest normal_bytes LEN
   ltac:(repeat constructor;vm_compute;discriminate) ltac:(cbn;lia))
   as [cell [base [input [mode INPUT]]]].
 destruct (sender_complete_report_exists cell base Int.one sequence input 0 r digest mode normal_bytes sender_literal_location INPUT)
   as [events [after [RUN [BYTES POST]]]].
 rewrite standard_descriptor_frame in BYTES.
 exists cell,base,input,mode,events,after.
 split; [exact INPUT|]. split; [exact RUN|]. split; [exact BYTES|].
 rewrite BYTES; apply imported_complete_frame; exact LEN.
Qed.
