(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-wire.failure: Setup fields preserve the actual child-report words under explicit byte provenance. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Values Memory Clight.
Require Import Machine LibraryMachine ResultLayout ReportingTrace FrameBytes
  FailureSourceDraft FailureMemoryDraft FailureContractDraft FailureTrace
  ReceiverSource ReceiverInput ReceiverReadStep ReceiverAccepted
  WireFailure WireReceiverFields.
Open Scope Z_scope.
Theorem wire_failure_receiver_observation_connection : forall
    ccell cbase cfd stage error mode mode_bytes drop short child_events child_target
    rcell rbase output ofs rfd bad entered done status run uid receiver_events value after,
  failure_input ccell cbase mode mode_bytes drop short ->
  library_steps failure_ge ccell(live(failure_initial cfd stage error Kstop cbase))child_events child_target ->
  receiver_input rcell rbase output ofs run uid ->
  library_steps result_ge rcell(live(receiver_initial output ofs rfd bad entered done status Kstop rbase))receiver_events
    (live(Returnstate value Kstop after)) ->
  receiver_read_trace receiver_events=reporting_trace child_events ->
  Mem.load Mint32 after output ofs=Some(Vint Int.one) ->
  receiver_read_trace receiver_events=failure_packet stage error /\
  result_contents after output ofs Int.one stage error Int.zero uid run /\
  bad=Int.zero /\ entered=Int.zero /\ 1<=Int.unsigned stage<=8 /\ 1<=Int.unsigned error<=4095.
Proof.
  intros ccell cbase cfd stage error mode mode_bytes drop short child_events child_target
    rcell rbase output ofs rfd bad entered done status run uid receiver_events value after
    CINPUT CHILD RINPUT RECEIVE PROVENANCE KIND.
  destruct(receiver_actual_setup_bounds _ _ _ _ _ _ _ _ _ _ _ _ _ _ RINPUT RECEIVE KIND)
    as[LEN[BAD[ENTERED[STAGE ERROR]]]].
  destruct(failure_reporting_prefix _ _ _ _ _ _ _ _ _ Kstop _ _ CINPUT I CHILD)as[rest PREFIX].
  change(selected_report mode_bytes stage error=reporting_trace child_events++rest)in PREFIX.
  rewrite <-PROVENANCE in PREFIX.
  destruct(wire_eight_byte_prefix_exact _ _ _ _ _ PREFIX LEN)as[PACKET EMPTY].
  pose proof(wire_receiver_setup_contents _ _ _ _ _ _ _ _ _ _ _ _ _ _ RINPUT RECEIVE KIND)as CONTENT.
  destruct(wire_failure_fields stage error)as[FS FE].
  rewrite PACKET,FS,FE in CONTENT.
  rewrite PACKET,FS in STAGE;rewrite PACKET,FE in ERROR.
  split;[exact PACKET|]. split;[exact CONTENT|]. split;[exact BAD|]. split;[exact ENTERED|]. split;assumption.
Qed.
