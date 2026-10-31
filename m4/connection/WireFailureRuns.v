(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-wire.evidence: Complete child/receiver histories share the actual eight-byte packet. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers Values Memory Clight.
Require Import Machine LibraryMachine LibraryWitnesses ProcessEffects ResultLayout ReportingTrace
  FailureSourceDraft FailureMemoryDraft FailureContractDraft FailureWitnesses
  ReceiverSource ReceiverInput ReceiverReadStep ReceiverTerminalRuns ReceiverFaultRuns ReceiverSamples
  WireFailure.
Import ListNotations.
Open Scope Z_scope.
Theorem wire_failure_receiver_owned_pair : forall waits retries,
  exists ccell cbase mode child_events child_after rcell rbase output receiver_events receiver_after,
  failure_input ccell cbase mode normal_bytes 21%positive 23%positive /\
  library_steps failure_ge ccell(live(failure_initial(Int.repr 3)Int.one(Int.repr 13)Kstop cbase))child_events(dead child_after) /\
  receiver_input rcell rbase output 0(Int64.repr 1)(Int.repr 1000) /\
  library_steps result_ge rcell(live(receiver_initial output 0(Int.repr 3)Int.zero Int.zero Int.one Int.zero Kstop rbase))
    receiver_events(live(Returnstate Vundef Kstop receiver_after)) /\
  receiver_read_trace receiver_events=reporting_trace child_events /\
  receiver_retries_observed retries receiver_events /\
  receiver_close_observed(Int.repr 3)(close_error(Int.repr 9))waits receiver_events /\
  result_contents receiver_after output 0 Int.one Int.one(Int.repr 13)Int.zero(Int.repr 1000)(Int64.repr 1).
Proof.
  intros waits retries.
  destruct(normal_failure_execution(Int.repr 3)Int.one(Int.repr 13))as[ccell[cbase[mode[child[child_after[CINPUT[CHILD BYTES]]]]]]].
  destruct(receiver_setup_actual_run waits retries)as[rcell[rbase[output[received[receiver_after[RINPUT[RECEIVE[READ[RETRIES[CLOSE CONTENT]]]]]]]]]].
  change(reporting_trace child=failure_packet Int.one(Int.repr 13))in BYTES.
  exists ccell,cbase,mode,(child++[exit_requested(Int.repr 125)]),child_after,rcell,rbase,output,received,receiver_after.
  split;[exact CINPUT|]. split;[exact CHILD|]. split;[exact RINPUT|]. split;[exact RECEIVE|]. split.
  - rewrite reporting_trace_app,BYTES;cbn [reporting_trace reporting_bytes flat_map];rewrite app_nil_r,wire_failure_packet;exact READ.
  - split;[exact RETRIES|]. split;assumption.
Qed.
