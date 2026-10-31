(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.evidence: Allocated successful normal, dropped, short, duplicate and malformed reports. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers Values Memory Clight.
Require Import Machine Library LibraryMachine LibraryWitnesses ResultLayout ReportingTrace FrameRecord
  SenderSelectors SenderGlobals SenderWitnesses SenderProgram SenderSource SenderSuccessfulRuns
  SenderFailedRuns SenderLossRuns.
Import ListNotations.
Open Scope Z_scope.
Definition sender_sample_record : frame_result :=
  {|fr_kind:=Int.zero;fr_stage:=Int.zero;fr_detail:=Int.zero;fr_entry:=Int.one;
    fr_clean:=Int.zero;fr_triggers:=Int.zero;fr_uid:=Int.zero;fr_run:=Int64.zero;
    fr_cpu:=Int64.zero;fr_peak:=Int64.zero;fr_out:=Int64.zero;fr_err:=Int64.zero;fr_elapsed:=Int64.zero;
    fr_oom:=Int64.zero;fr_pids:=Int64.zero;fr_export_state:=Int.zero;fr_omitted:=Int.zero;fr_export_error:=Int.zero|}.
Definition sender_sample_digest := repeat Byte.zero 32.
Definition sender_sample_modes : list (list Byte.int * nat) :=
  [(normal_bytes,160%nat);(report_name drop_frame,0%nat);(report_name short_frame,17%nat);
   (report_name duplicate_frame,320%nat);(report_name wrong_sequence,160%nat);(report_name bad_reserved,160%nat)].
Theorem sender_sample_mode_facts : Forall (fun sample=>
  Forall (fun b=>b<>Byte.zero) (fst sample) /\ (length (fst sample)<=158)%nat /\
  length (sender_expected (Int.repr 2) Int64.mone sender_sample_record sender_sample_digest (fst sample))=snd sample)
  sender_sample_modes.
Proof.
  unfold sender_sample_modes;repeat (apply Forall_cons;
    [split;[repeat constructor;vm_compute;discriminate|split;[cbn;lia|vm_compute;reflexivity]]|]);constructor.
Qed.
Theorem sender_sample_successful_executions : forall mode_bytes count,
  In (mode_bytes,count) sender_sample_modes ->
  exists cell base input mode events after,
    sender_input cell base input 0 sender_sample_record sender_sample_digest mode mode_bytes sender_literal_location /\
    library_steps result_ge cell (live (sender_initial (Int.repr 2) Int64.mone input 0 Kstop base)) events
      (live (Returnstate (Vint Int.zero) Kstop after)) /\
    reporting_trace events=sender_expected (Int.repr 2) Int64.mone sender_sample_record sender_sample_digest mode_bytes /\
    length (reporting_trace events)=count.
Proof.
  intros mode_bytes count IN;pose proof sender_sample_mode_facts as FACTS;rewrite Forall_forall in FACTS.
  destruct (FACTS _ IN) as [NONZERO [SIZE COUNT]];cbn [fst snd] in *.
  destruct (arbitrary_sender_input sender_sample_record sender_sample_digest mode_bytes eq_refl NONZERO SIZE)
    as [cell [base [input [mode INPUT]]]].
  destruct (sender_complete_report_exists cell base (Int.repr 2) Int64.mone input 0 sender_sample_record
    sender_sample_digest mode mode_bytes sender_literal_location INPUT) as [events [after [RUN [BYTES RESULT]]]].
  exists cell,base,input,mode,events,after;split;[exact INPUT|]. split;[exact RUN|]. split;[exact BYTES|congruence].
Qed.
Theorem sender_sample_malformed_headers :
  firstn 8 (skipn 16 (sender_expected (Int.repr 2) Int64.mone sender_sample_record sender_sample_digest (report_name wrong_sequence)))=
    repeat Byte.zero 8 /\
  nth 28 (sender_expected (Int.repr 2) Int64.mone sender_sample_record sender_sample_digest (report_name bad_reserved)) Byte.zero=Byte.one.
Proof. split;vm_compute;reflexivity. Qed.
Theorem sender_sample_failed_execution : exists cell base input mode events after,
  sender_input cell base input 0 sender_sample_record sender_sample_digest mode normal_bytes sender_literal_location /\
  library_steps result_ge cell (live (sender_initial (Int.repr 2) Int64.mone input 0 Kstop base)) events
    (live (Returnstate (Vint Int.mone) Kstop after)) /\ reporting_trace events=[].
Proof.
  destruct (arbitrary_sender_input sender_sample_record sender_sample_digest normal_bytes eq_refl
    ltac:(repeat constructor;vm_compute;discriminate) ltac:(cbn;lia)) as [cell [base [input [mode INPUT]]]].
  destruct (sender_failed_report_exists cell base (Int.repr 2) Int64.mone input 0 sender_sample_record
    sender_sample_digest mode normal_bytes sender_literal_location (Int.repr 5) INPUT
    ltac:(vm_compute;discriminate) ltac:(vm_compute;discriminate)) as [events [after [RUN [EMPTY RESULT]]]].
  exists cell,base,input,mode,events,after;auto.
Qed.
Theorem sender_sample_partial_loss : forall waits,exists cell base input mode events after byte rest,
  sender_input cell base input 0 sender_sample_record sender_sample_digest mode normal_bytes sender_literal_location /\
  library_steps result_ge cell (live (sender_initial (Int.repr 2) Int64.mone input 0 Kstop base)) events (dead after) /\
  reporting_trace events=[byte] /\
  sender_expected (Int.repr 2) Int64.mone sender_sample_record sender_sample_digest normal_bytes=byte::rest /\
  exists before request,events=before++map original_event (repeat wait_step waits++[partial_loss request [byte] None]).
Proof.
  intros waits;destruct (arbitrary_sender_input sender_sample_record sender_sample_digest normal_bytes eq_refl
    ltac:(repeat constructor;vm_compute;discriminate) ltac:(cbn;lia)) as [cell [base [input [mode INPUT]]]].
  destruct (sender_one_byte_loss_exists waits cell base (Int.repr 2) Int64.mone input 0 sender_sample_record
    sender_sample_digest mode normal_bytes sender_literal_location INPUT ltac:(vm_compute;discriminate))
    as [events [after [byte [rest [RUN [BYTES [FRAME [PRESERVED SHAPE]]]]]]]].
  exists cell,base,input,mode,events,after,byte,rest;split;[exact INPUT|]. split;[exact RUN|].
  split;[exact BYTES|]. split;assumption.
Qed.
