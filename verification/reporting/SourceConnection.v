(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-reporting.proof: The full helper source consumes the ordinary Lean publication theorem. *)
From Stdlib Require Import ZArith List Lia FunctionalExtensionality.
From compcert Require Import Integers Values Clight.
From LeanImport Require Import Lean.
Require Import NormalizedImport ReportingImport CallProjection BridgeNat BridgeBytes FrameNumbers FrameHeader FrameFields FrameEquality WireFields
 Machine LibraryMachine ResultLayout ReportingTrace FrameRecord SenderSource SenderProgram SenderOutcomes SenderWriteReturn.
Local Close Scope lean_scope.
Local Open Scope Z_scope.
Import ListNotations.

Definition source_frame sequence r digest := LeanCage_Reporting_Frame_mk
 (Bool_not (Nat_beq (imported_int64 sequence) Nat_zero))
 (imported_int32 (fr_entry r)) (imported_int32 (fr_clean r))
 (fun entry => imported_frame_result r digest entry).

Theorem source_frame_view sequence r digest : length digest=32%nat ->
 LeanCage_Reporting_FrameView (imported_bytes (outgoing_frame sequence r digest))
 (source_frame sequence r digest).
Proof.
 intro LEN;unfold LeanCage_Reporting_FrameView, source_frame.
 repeat apply And_intro.
 - change (Lean.eq (LeanCageM4_Normalized_headerBadBytes (imported_bytes (outgoing_frame sequence r digest)))
     (Bool_not (Nat_beq (imported_int64 sequence) Nat_zero))).
   rewrite imported_frame_header by exact LEN;constructor.
 - change (Lean.eq (LeanCageM4_Normalized_littleBytes (imported_bytes (outgoing_frame sequence r digest))
     (Nat_of_nat 40) (Nat_of_nat 4)) (imported_int32 (fr_entry r))).
   rewrite imported_little32_value,wire_entry;constructor.
 - change (Lean.eq (LeanCageM4_Normalized_littleBytes (imported_bytes (outgoing_frame sequence r digest))
     (Nat_of_nat 44) (Nat_of_nat 4)) (imported_int32 (fr_clean r))).
   rewrite imported_little32_value,wire_clean;constructor.
 - apply standard_equality_imported;apply functional_extensionality;intro entry.
   apply imported_frame_fields;exact LEN.
Qed.

Theorem source_sender_view cell base sequence input ofs r digest mode mode_bytes locations events after :
 sender_input cell base input ofs r digest mode mode_bytes locations ->
 library_steps result_ge cell (live (sender_initial Int.one sequence input ofs Kstop base)) events
   (live (Returnstate (Vint Int.zero) Kstop after)) ->
 LeanCage_Reporting_FrameView (imported_bytes (reporting_trace events)) (source_frame sequence r digest).
Proof.
 intros INPUT RUN.
 destruct (sender_all_returns _ _ _ _ _ _ _ _ _ _ _ _ _ _ INPUT RUN)
   as [_ [[VALUE BYTES]|[VALUE FAILED]]];[|discriminate].
 rewrite standard_descriptor_frame in BYTES;rewrite BYTES.
 apply source_frame_view;exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj1 INPUT)))))).
Qed.

Theorem source_sender_decoder cell base sequence input ofs r digest mode mode_bytes locations events after :
 sender_input cell base input ofs r digest mode mode_bytes locations ->
 library_steps result_ge cell (live (sender_initial Int.one sequence input ofs Kstop base)) events
   (live (Returnstate (Vint Int.zero) Kstop after)) ->
 Lean.eq (LeanCageM4_Normalized_decode (imported_bytes (reporting_trace events)))
   (LeanCage_Reporting_decodeFrame (source_frame sequence r digest)).
Proof.
 intros INPUT RUN.
 destruct(sender_all_prefixes _ _ _ _ _ _ _ _ _ _ _ _ _ INPUT RUN)as[_ [rest PREFIX]].
 rewrite standard_descriptor_frame in PREFIX.
 eapply (LeanCage_Reporting_normalized_publication
   (imported_bytes(outgoing_frame sequence r digest))
   (imported_bytes(reporting_trace events)) (imported_list(List.map imported_byte rest))
   (source_frame sequence r digest)).
 - apply source_frame_view;exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj1 INPUT)))))).
 - pose proof(source_call_interface cell base sequence input ofs r digest mode mode_bytes locations events
     (live(Returnstate(Vint Int.zero)Kstop after)) rest INPUT RUN PREFIX)as CALL.
   change (LeanCage_Reporting_Call (imported_bytes(outgoing_frame sequence r digest))
     (imported_bytes(reporting_trace events)) (imported_list(List.map imported_byte rest))
     LeanCage_Reporting_Status_published) in CALL.
   exact CALL.
Qed.
