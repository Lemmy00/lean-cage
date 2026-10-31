(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-decoder.evidence: Useful real executions, arbitrary waits, and loss at every live boundary. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers Values Memory Events Clight.
Require Import Machine Deterministic StoreSteps LibraryMachine LibraryControl Fault
  ResultLayout ResultSafety FreshMemory DecoderSource DecoderCompare DecoderInput
  DecoderProgram ComparisonGuarantees.
Import ListNotations.
Lemma decoder_source_events_progress : forall n,
  Forall control_progress (map original_event (repeat (source_step E0) n)).
Proof.
  induction n;cbn;constructor;[|exact IHn]. unfold control_progress;cbn;repeat split;discriminate.
Qed.
Theorem decoder_finite_return_exists : forall cell base p bytes output ofs run uid preflight sequence,
  decoder_input base p bytes output ofs run uid preflight ->
  exists events value after,
    library_steps result_ge cell (live (decoder_initial p sequence output ofs Kstop base)) events
      (live (Returnstate value Kstop after)) /\ Forall control_progress events /\
    decoder_result base bytes output ofs run uid preflight sequence value after.
Proof.
  intros cell base p bytes output ofs run uid preflight sequence INPUT.
  destruct (decoder_source_connection cell base p bytes output ofs run uid preflight sequence INPUT)
    as [memories [magic [count [PATH [OWN RETURN]]]]].
  destruct (memcmp_caller_run result_ge cell _ _ _ _ _ _ _ OWN RETURN)
    as [events [value [after [RUN [PROGRESS POST]]]]].
  exists (map original_event (repeat (source_step E0) count)++events),value,after.
  split.
  - eapply library_steps_trans;[apply original_runs_preserved;eapply store_path_actual;exact PATH|exact RUN].
  - split;[apply Forall_app;split;[apply decoder_source_events_progress|exact PROGRESS]|exact POST].
Qed.
Theorem decoder_arbitrary_waits_and_loss : forall waits cell base p bytes output ofs run uid preflight sequence,
  decoder_input base p bytes output ofs run uid preflight ->
  exists count allocated,
    library_steps result_ge cell (live (decoder_initial p sequence output ofs Kstop base))
      (map original_event (repeat (source_step E0) count)++repeat library_wait waits++[original_event loss_step])
      (dead allocated) /\ old_memory base allocated.
Proof.
  intros waits cell base p bytes output ofs run uid preflight sequence INPUT.
  destruct (decoder_source_connection cell base p bytes output ofs run uid preflight sequence INPUT)
    as [memories [magic [count [PATH [OWN RETURN]]]]].
  exists count,(decoder_allocated _ _ _ _ memories). split;[|apply decoder_allocated_old].
  eapply library_steps_trans;[apply original_runs_preserved;eapply store_path_actual;exact PATH|].
  apply library_arbitrary_wait_then_loss. apply memcmp_ready;exact OWN.
Qed.
Theorem decoder_loss_from_every_live_prefix : forall cell base p bytes output ofs run uid preflight sequence events s,
  decoder_input base p bytes output ofs run uid preflight ->
  library_steps result_ge cell (live (decoder_initial p sequence output ofs Kstop base)) events (live s) ->
  library_steps result_ge cell (live (decoder_initial p sequence output ofs Kstop base))
    (events++[original_event loss_step]) (dead (memory_of s)) /\
  result_preserved base output ofs (memory_of s).
Proof.
  intros cell base p bytes output ofs run uid preflight sequence events s INPUT RUN. split.
  - eapply library_steps_trans;[exact RUN|]. econstructor;[apply library_loss_everywhere|constructor].
  - exact (decoder_all_prefixes cell base p bytes output ofs run uid preflight sequence events (live s) INPUT RUN).
Qed.
