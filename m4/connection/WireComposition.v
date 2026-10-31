(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-wire.composition: Actual publication bytes connected to actual private decoding. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers Values Memory Clight.
Require Import Machine LibraryMachine ResultLayout ReportingTrace FrameRecord SenderSelectors SenderSource
  SenderProgram SenderOutcomes DecoderSource DecoderInput
  WireSource.
Import ListNotations.
Open Scope Z_scope.
Theorem wire_source_observation_connection : forall
    scell sbase fd sequence input input_ofs r digest mode mode_bytes locations sent sender_after
    dcell dbase p output ofs run uid preflight expected_sequence received value decoder_after,
  sender_input scell sbase input input_ofs r digest mode mode_bytes locations ->
  report_enabled fd r=false ->
  library_steps result_ge scell(live(sender_initial fd sequence input input_ofs Kstop sbase))sent
    (live(Returnstate(Vint Int.zero)Kstop sender_after)) ->
  decoder_input dbase p(reporting_trace sent)output ofs run uid preflight ->
  library_steps result_ge dcell(live(decoder_initial p expected_sequence output ofs Kstop dbase))received
    (live(Returnstate value Kstop decoder_after)) ->
  wire_decode_result dbase output ofs sequence r digest run uid preflight expected_sequence value decoder_after.
Proof.
  intros scell sbase fd sequence input input_ofs r digest mode mode_bytes locations sent sender_after
    dcell dbase p output ofs run uid preflight expected_sequence received value decoder_after SINPUT DISABLED SEND DINPUT DECODE.
  destruct(sender_all_returns _ _ _ _ _ _ _ _ _ _ _ _ _ _ SINPUT SEND)
    as[_[[VALUE BYTES]|[VALUE OTHER]]];[|discriminate VALUE].
  rewrite(disabled_selector_frame fd sequence r digest mode_bytes DISABLED)in BYTES.
  rewrite BYTES in DINPUT;eapply wire_decoder_source_return;[exact DINPUT|exact DECODE].
Qed.
