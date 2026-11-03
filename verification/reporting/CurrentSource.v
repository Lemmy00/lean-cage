(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-reporting.proof: The publication argument uses the actual complete helper program. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Ctypes Clight.
From LeanImport Require Import Lean.
From LeanCageMain Require Main.
Require Import Slice NormalizedImport ReportingImport BridgeNat BridgeBytes FrameEquality
 Machine Library LibraryMachine ReportingTrace ResultLayout DecoderValidity FrameRecord SenderSource SenderProgram SenderOutcomes
 SenderSuccessfulRuns SenderFailedRuns SenderLossRuns CallProjection SourceConnection InputWitnesses.
Local Close Scope lean_scope.
Local Open Scope Z_scope.
Import ListNotations.

Theorem current_program_exact : Slice.prog=Main.prog.
Proof. reflexivity. Qed.
Theorem current_sender_exact : Slice.f_send_frame=Main.f_send_frame.
Proof. reflexivity. Qed.

Theorem current_sender_decodes cell base sequence input ofs r digest mode mode_bytes locations events after :
 sender_input cell base input ofs r digest mode mode_bytes locations ->
 library_steps (Clight.globalenv Main.prog) cell
   (live(Callstate(Internal Main.f_send_frame)
     [Vint Int.one;Vlong sequence;Vptr input(Ptrofs.repr ofs)]Kstop base)) events
   (live(Returnstate(Vint Int.zero)Kstop after)) ->
 LeanCageM4_Normalized_decode(imported_bytes(reporting_trace events))=
   LeanCage_Reporting_decodeFrame(source_frame sequence r digest).
Proof.
 intros INPUT RUN;apply imported_equality_standard.
 eapply source_sender_decoder;[exact INPUT|exact RUN].
Qed.

Theorem current_sender_nonvacuous sequence r digest : length digest=32%nat ->
 exists cell base input mode events after,
 sender_input cell base input 0 r digest mode [] sender_literal_location /\
 library_steps result_ge cell
   (live(sender_initial Int.one sequence input 0 Kstop base)) events
   (live(Returnstate(Vint Int.zero)Kstop after)) /\
 reporting_trace events=outgoing_frame sequence r digest.
Proof.
 intro LEN.
 destruct(arbitrary_sender_input r digest [] LEN (Forall_nil _) ltac:(cbn;lia))
 as[cell[base[input[mode INPUT]]]].
 destruct(sender_complete_report_exists cell base Int.one sequence input 0 r digest mode [] sender_literal_location INPUT)
 as[events[after[RUN[BYTES POST]]]].
 exists cell,base,input,mode,events,after;split;[exact INPUT|]. split;[exact RUN|].
 rewrite standard_descriptor_frame in BYTES;exact BYTES.
Qed.

Theorem current_sender_failure sequence r digest : length digest=32%nat ->
 exists cell base input mode events after,
 sender_input cell base input 0 r digest mode [] sender_literal_location /\
 library_steps result_ge cell
   (live(sender_initial Int.one sequence input 0 Kstop base)) events
   (live(Returnstate(Vint Int.mone)Kstop after)) /\
 reporting_trace events=[] /\
 LeanCageM4_Normalized_decode(imported_bytes(reporting_trace events))=
   Except_error_inst3 LeanCageM4_Normalized_ErrorCode LeanCageM3_Result LeanCageM4_Normalized_ErrorCode_header.
Proof.
 intro LEN.
 destruct(arbitrary_sender_input r digest [] LEN (Forall_nil _) ltac:(cbn;lia))
 as[cell[base[input[mode INPUT]]]].
 assert(NONEMPTY : sender_expected Int.one sequence r digest []<>[]).
 { rewrite standard_descriptor_frame;unfold outgoing_frame,frame_magic;discriminate. }
 destruct(sender_failed_report_exists cell base Int.one sequence input 0 r digest mode [] sender_literal_location
   (Int.repr 5) INPUT NONEMPTY ltac:(vm_compute;discriminate)) as[events[after[RUN[EMPTY POST]]]].
 exists cell,base,input,mode,events,after;split;[exact INPUT|]. split;[exact RUN|].
 split;[exact EMPTY|rewrite EMPTY;reflexivity].
Qed.

Theorem current_sender_partial_loss waits sequence r digest : length digest=32%nat ->
 exists cell base input mode events after byte,
 sender_input cell base input 0 r digest mode [] sender_literal_location /\
 library_steps result_ge cell
   (live(sender_initial Int.one sequence input 0 Kstop base)) events (dead after) /\
 reporting_trace events=[byte] /\
 LeanCageM4_Normalized_decode(imported_bytes(reporting_trace events))=
   Except_error_inst3 LeanCageM4_Normalized_ErrorCode LeanCageM3_Result LeanCageM4_Normalized_ErrorCode_header /\
 exists before request,events=before++List.map original_event (repeat wait_step waits++[partial_loss request [byte] None]).
Proof.
 intro LEN.
 destruct(arbitrary_sender_input r digest [] LEN (Forall_nil _) ltac:(cbn;lia))
 as[cell[base[input[mode INPUT]]]].
 assert(NONEMPTY : sender_expected Int.one sequence r digest []<>[]).
 { rewrite standard_descriptor_frame;unfold outgoing_frame,frame_magic;discriminate. }
 destruct(sender_one_byte_loss_exists waits cell base Int.one sequence input 0 r digest mode [] sender_literal_location
   INPUT NONEMPTY) as[events[after[byte[rest[RUN[BYTES[EXPECTED[PRESERVED HISTORY]]]]]]]].
 exists cell,base,input,mode,events,after,byte;split;[exact INPUT|]. split;[exact RUN|].
 split;[exact BYTES|]. split;[rewrite BYTES;reflexivity|exact HISTORY].
Qed.
