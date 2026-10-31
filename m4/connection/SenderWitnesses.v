(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.evidence: Actual allocation witnesses inhabit whole-source inputs and executions. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers Values Memory Clight.
Require Import Machine Library LibraryMachine FreshMemory ResultLayout DecoderAllocation SenderSelectors
  FrameRecord FrameAllocation SenderGlobals SenderSource SenderProgram SenderRuns ReportingTrace.
Import ListNotations.
Open Scope Z_scope.
Theorem arbitrary_sender_input : forall r digest mode_bytes,
  length digest=32%nat -> Forall (fun b=>b<>Byte.zero) mode_bytes -> (length mode_bytes<=158)%nat ->
  exists cell base input mode,sender_input cell base input 0 r digest mode mode_bytes sender_literal_location.
Proof.
  intros r digest mode_bytes LEN NONZERO SIZE.
  destruct (allocated_sender_globals mode_bytes NONZERO SIZE) as [cell [globals [mode [SELECTORS MAGIC]]]].
  destruct (allocate_frame_record globals r digest LEN) as [base [input [OLD [OWN BLOCK]]]].
  exists cell,base,input,mode;split;[exact OWN|]. split;[eapply sender_selectors_old;eassumption|].
  exists 25%positive;split;[exact (proj1 source_decoder_global_symbols)|eapply old_memory_readable;eassumption].
Qed.
Theorem arbitrary_sender_executes : forall fd sequence r digest mode_bytes,
  length digest=32%nat -> Forall (fun b=>b<>Byte.zero) mode_bytes -> (length mode_bytes<=158)%nat ->
  exists cell base input mode events value after,
    sender_input cell base input 0 r digest mode mode_bytes sender_literal_location /\
    library_steps result_ge cell (live (sender_initial fd sequence input 0 Kstop base)) events
      (live (Returnstate value Kstop after)) /\
    sender_result base (sender_expected fd sequence r digest mode_bytes) (reporting_trace events) value after.
Proof.
  intros fd sequence r digest mode_bytes LEN NONZERO SIZE.
  destruct (arbitrary_sender_input r digest mode_bytes LEN NONZERO SIZE) as [cell [base [input [mode INPUT]]]].
  destruct (sender_finite_return_exists _ _ fd sequence _ _ _ _ _ _ _ INPUT)
    as [events [value [after [RUN POST]]]].
  exists cell,base,input,mode,events,value,after;auto.
Qed.
