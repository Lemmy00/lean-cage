(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-bridge.frames: Exact imported frame operations and source observations. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers Values Clight.
From LeanImport Require Import Lean.
Require Import NormalizedImport BridgeBytes Machine LibraryMachine LibraryWitnesses ResultLayout ReportingTrace
 FrameRecord SenderGlobals SenderSource SenderProgram
 FrameFields FrameComplete FrameExecution.
Local Close Scope lean_scope.
Local Open Scope Z_scope.
Import ListNotations.

Definition frame_sample_record kind stage detail entry clean triggers run uid export_state export_error : frame_result :=
 {| fr_kind:=Int.repr kind; fr_stage:=Int.repr stage; fr_detail:=Int.repr detail; fr_entry:=Int.repr entry;
    fr_clean:=Int.repr clean; fr_triggers:=Int.repr triggers; fr_uid:=Int.repr uid; fr_run:=Int64.repr run;
    fr_cpu:=Int64.zero; fr_peak:=Int64.zero; fr_out:=Int64.zero; fr_err:=Int64.zero; fr_elapsed:=Int64.zero;
    fr_oom:=Int64.zero; fr_pids:=Int64.zero; fr_export_state:=Int.repr export_state;
    fr_omitted:=Int.zero; fr_export_error:=Int.repr export_error |}.
Record frame_sample := {
 sample_sequence : int64; sample_record : frame_result; sample_digest : list Byte.int;
 sample_error : option LeanCageM4_Normalized_ErrorCode
}.
Definition frame_case sequence kind stage detail entry clean triggers run uid export_state export_error digest error :=
 {| sample_sequence:=Int64.repr sequence;
    sample_record:=frame_sample_record kind stage detail entry clean triggers run uid export_state export_error;
    sample_digest:=digest; sample_error:=error |}.
Definition frame_samples := [
 frame_case 0 0 0 42 1 1 0 1 100000 0 0 (repeat Byte.zero 32) None;
 frame_case 0 1 8 13 0 1 0 1 100000 0 0 (repeat Byte.zero 32) None;
 frame_case 0 2 0 9 1 1 0 1 100000 0 0 (repeat Byte.zero 32) None;
 frame_case 0 3 0 0 1 0 1 1 100000 0 0 (repeat Byte.zero 32) None;
 frame_case 0 4 9 71 2 0 0 1 100000 0 0 (repeat Byte.zero 32) None;
 frame_case 0 7 0 0 0 1 0 0 0 0 0 (repeat Byte.zero 32) None;
 frame_case 0 256 0 42 1 1 0 1 100000 0 0 (repeat Byte.zero 32) None;
 frame_case 0 0 0 42 1 1 0 1 100000 1 0 (repeat (Byte.repr 173) 32) None;
 frame_case 0 0 0 42 1 1 0 1 100999 2 13 (repeat Byte.zero 32) None;
 frame_case 0 5 0 0 0 1 0 1 100000 0 0 (repeat Byte.zero 32) (Some LeanCageM4_Normalized_ErrorCode_validity);
 frame_case 0 6 8 0 1 1 0 1 100000 0 0 (repeat Byte.zero 32) (Some LeanCageM4_Normalized_ErrorCode_validity);
 frame_case 0 2 0 65 1 1 0 1 100000 0 0 (repeat Byte.zero 32) (Some LeanCageM4_Normalized_ErrorCode_validity);
 frame_case 0 0 0 42 1 1 0 1 101000 0 0 (repeat Byte.zero 32) (Some LeanCageM4_Normalized_ErrorCode_validity);
 frame_case 0 0 0 42 1 1 0 1 100000 0 0 (repeat (Byte.repr 173) 32) (Some LeanCageM4_Normalized_ErrorCode_validity);
 frame_case 0 0 0 42 1 1 0 1 100000 2 0 (repeat Byte.zero 32) (Some LeanCageM4_Normalized_ErrorCode_validity);
 frame_case 0 0 0 42 3 2 0 1 100000 0 0 (repeat Byte.zero 32) (Some LeanCageM4_Normalized_ErrorCode_entry);
 frame_case 0 0 0 42 1 2 0 1 100000 0 0 (repeat Byte.zero 32) (Some LeanCageM4_Normalized_ErrorCode_cleanup);
 frame_case 1 5 0 0 3 2 0 1 100000 0 0 (repeat Byte.zero 32) (Some LeanCageM4_Normalized_ErrorCode_header)
].
Definition frame_sample_expected s := match sample_error s with
 | Some error => Except_error_inst3 LeanCageM4_Normalized_ErrorCode LeanCageM3_Result error
 | None => Except_ok_inst3 LeanCageM4_Normalized_ErrorCode LeanCageM3_Result
   (imported_frame_result (sample_record s) (sample_digest s)
     (match Z.to_nat (Int.unsigned (fr_entry (sample_record s))) with
      | 0%nat => LeanCageM3_Entry_no | 1%nat => LeanCageM3_Entry_yes | _ => LeanCageM3_Entry_unknown end))
 end.
Theorem frame_samples_checked : Forall (fun s =>
 source_complete_decode (sample_sequence s) (sample_record s) (sample_digest s) = frame_sample_expected s) frame_samples.
Proof. unfold frame_samples; repeat (apply Forall_cons; [reflexivity|]); constructor. Qed.
Theorem frame_samples_lengths : Forall (fun s => length (sample_digest s)=32%nat) frame_samples.
Proof. unfold frame_samples; repeat (apply Forall_cons; [reflexivity|]); constructor. Qed.
Theorem frame_samples_actual_source s : In s frame_samples ->
 exists cell base input mode events after,
 sender_input cell base input 0 (sample_record s) (sample_digest s) mode normal_bytes sender_literal_location /\
 library_steps result_ge cell (live (sender_initial Int.one (sample_sequence s) input 0 Kstop base)) events
   (live (Returnstate (Vint Int.zero) Kstop after)) /\
 reporting_trace events=outgoing_frame (sample_sequence s) (sample_record s) (sample_digest s) /\
 LeanCageM4_Normalized_decode (imported_bytes (reporting_trace events)) = frame_sample_expected s.
Proof.
 intro IN; pose proof frame_samples_checked as CHECK; pose proof frame_samples_lengths as LENGTH.
 rewrite Forall_forall in CHECK,LENGTH.
 destruct (source_sender_imported_nonvacuous (sample_record s) (sample_digest s) (sample_sequence s) (LENGTH s IN))
   as [cell [base [input [mode [events [after [INPUT [RUN [BYTES DECODE]]]]]]]]].
 exists cell,base,input,mode,events,after; rewrite (CHECK s IN) in DECODE; auto.
Qed.
