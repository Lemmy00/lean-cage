(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-wire.evidence: Allocated complete source pairs for every field combination. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers Values Memory Clight.
Require Import Machine Library LibraryWitnesses LibraryMachine ResultLayout ReportingTrace FrameRecord SenderSelectors
  SenderGlobals SenderWitnesses SenderSource SenderProgram SenderSuccessfulRuns SenderOutcomes
  DecoderSource DecoderInput DecoderProgram DecoderAllocation DecoderRuns WireSource.
Import ListNotations.
Open Scope Z_scope.
Theorem wire_allocated_source_pair : forall r digest sequence run uid preflight expected_sequence,
  length digest=32%nat -> exists cell sbase input mode sent sender_after dbase p output received value decoder_after,
  sender_input cell sbase input 0 r digest mode normal_bytes sender_literal_location /\
  library_steps result_ge cell(live(sender_initial Int.one sequence input 0 Kstop sbase))sent
    (live(Returnstate(Vint Int.zero)Kstop sender_after)) /\
  reporting_trace sent=outgoing_frame sequence r digest /\
  decoder_input dbase p(reporting_trace sent)output 0 run uid preflight /\
  library_steps result_ge cell(live(decoder_initial p expected_sequence output 0 Kstop dbase))received
    (live(Returnstate value Kstop decoder_after)) /\
  wire_decode_result dbase output 0 sequence r digest run uid preflight expected_sequence value decoder_after.
Proof.
  intros r digest sequence run uid preflight expected_sequence LEN.
  destruct(arbitrary_sender_input r digest normal_bytes LEN
    ltac:(repeat constructor;vm_compute;discriminate)ltac:(cbn;lia))as[cell[sbase[input[mode INPUT]]]].
  destruct(sender_complete_report_exists cell sbase Int.one sequence input 0 r digest mode normal_bytes sender_literal_location INPUT)
    as[sent[sender_after[SEND[BYTES RESULT]]]].
  rewrite standard_descriptor_frame in BYTES.
  destruct(arbitrary_decoder_source_input(outgoing_frame sequence r digest)run uid preflight
    (outgoing_frame_length sequence r digest LEN))as[dbase[p[output DINPUT]]].
  destruct(decoder_finite_return_exists cell dbase p _ output 0 run uid preflight expected_sequence DINPUT)
    as[received[value[decoder_after[DECODE[PROGRESS POST]]]]].
  exists cell,sbase,input,mode,sent,sender_after,dbase,p,output,received,value,decoder_after.
  split;[exact INPUT|]. split;[exact SEND|]. split;[exact BYTES|]. split;[rewrite BYTES;exact DINPUT|].
  split;[exact DECODE|]. eapply wire_decoder_source_return;[exact DINPUT|exact DECODE].
Qed.
