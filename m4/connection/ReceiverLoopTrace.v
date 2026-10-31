(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-receiver.reads: Terminal fields are classified from the exact bytes read on that execution. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Clight.
Require Import Slice Machine StoreSteps WriteAll Deterministic ResultLayout LibraryMachine CallProgress
  SourceGuarantees ReceiverSource ReceiverReadSource ReceiverReadMemory ReceiverRouting
  ReceiverReadReturns ReceiverReadStep ReceiverReadHistory ReceiverInput ReceiverChoice
  ReceiverConstruction ReceiverTerminal ReceiverTrace ReceiverTerminalTrace.
Import ListNotations.
Open Scope Z_scope.
Theorem receiver_stop_terminal : forall cell base b output ofs fd bad entered done status run uid bytes stopped,
  receiver_input cell base output ofs run uid ->
  receiver_at_stop cell b(receiver_temps output ofs fd bad entered done status)bad Kstop
    (receiver_live_memory cell base b output ofs fd)bytes stopped ->
  receiver_quiet result_ge cell stopped /\
  exists reason,receiver_stop_valid reason bytes /\
    procedure_guarantee result_ge cell(ReceiverMemory.receiver_preserved cell base output ofs)
      (receiver_choice_result output ofs(receiver_select bytes(receiver_bad bad reason)entered done status)uid run b)stopped.
Proof.
  intros cell base b output ofs fd bad entered done status run uid bytes stopped INPUT
    [le[m[reason[EQ[STOP[LIVE[BUFFER[KEEP[BAD USED]]]]]]]]];subst stopped.
  assert(OUT : le!__res=Some(Vptr output(Ptrofs.repr ofs))).
  { rewrite(KEEP __res ltac:(cbn;tauto));unfold receiver_temps;WriteAll.lookup. }
  assert(ENTERED : le!_entered=Some(Vint entered)).
  { rewrite(KEEP _entered ltac:(cbn;tauto));unfold receiver_temps;WriteAll.lookup. }
  assert(DONE : le!_leader_done=Some(Vint done)).
  { rewrite(KEEP _leader_done ltac:(cbn;tauto));unfold receiver_temps;WriteAll.lookup. }
  assert(STATUS : le!_leader_status=Some(Vint status)).
  { rewrite(KEEP _leader_status ltac:(cbn;tauto));unfold receiver_temps;WriteAll.lookup. }
  split.
  - eapply receiver_terminal_quiet;[exact INPUT|exact LIVE|exact BUFFER|exact OUT|exact BAD|exact ENTERED|exact DONE|exact STATUS|exact USED].
  - exists reason;split;[exact STOP|].
    eapply receiver_terminal_guarantee;[exact INPUT|exact LIVE|exact BUFFER|exact OUT|exact BAD|exact ENTERED|exact DONE|exact STATUS|exact USED].
Qed.
Theorem receiver_loop_exact_trace : forall cell base b output ofs fd bad entered done status run uid start events value after,
  receiver_input cell base output ofs run uid ->
  receiver_routed cell b fd(receiver_temps output ofs fd bad entered done status)bad Kstop
    (receiver_live_memory cell base b output ofs fd)[]start ->
  library_steps result_ge cell(live start)events(live(Returnstate value Kstop after)) ->
  exists reason,receiver_stop_valid reason(receiver_read_trace events) /\
    receiver_choice_result output ofs
      (receiver_select(receiver_read_trace events)(receiver_bad bad reason)entered done status)uid run b value after.
Proof.
  intros cell base b output ofs fd bad entered done status run uid start events value after INPUT ROUTED RUN.
  destruct(receiver_return_reaches_stop _ _ _ _ _ _ _ _ _ _ _ _
    (receiver_live_read _ _ _ _ _ _ (proj1(proj2 INPUT)))
    (receiver_live_descriptor _ _ _ _ _ _)ROUTED RUN)
    as[before[tail[stopped[ES[PRE[TAIL STOP]]]]]].
  cbn [app]in STOP.
  destruct(receiver_stop_terminal cell base b output ofs fd bad entered done status run uid
    (receiver_read_trace before)stopped INPUT STOP)as[QUIET[reason[VALID GUARANTEE]]].
  assert(TRACE : receiver_read_trace events=receiver_read_trace before).
  { rewrite ES,receiver_read_trace_app,(QUIET _ _ TAIL),app_nil_r;reflexivity. }
  rewrite TRACE;exists reason;split;[exact VALID|].
  eapply procedure_return_post;[exact(proj2 GUARANTEE)|exact TAIL].
Qed.
Theorem receiver_loop_read_bound : forall cell base b output ofs fd bad entered done status run uid start events target,
  receiver_input cell base output ofs run uid ->
  receiver_routed cell b fd(receiver_temps output ofs fd bad entered done status)bad Kstop
    (receiver_live_memory cell base b output ofs fd)[]start ->
  library_steps result_ge cell(live start)events target ->(length(receiver_read_trace events)<=9)%nat.
Proof.
  intros cell base b output ofs fd bad entered done status run uid start events target INPUT ROUTED RUN.
  destruct(receiver_read_prefix_bound _ _ _ _ _ _ _ _ _ _ _
    (receiver_live_read _ _ _ _ _ _ (proj1(proj2 INPUT)))
    (receiver_live_descriptor _ _ _ _ _ _)ROUTED RUN)as[BOUND|STOP];[exact BOUND|].
  destruct STOP as[before[tail[stopped[ES[PRE[TAIL STOP]]]]]];cbn [app]in STOP.
  pose proof(proj1(receiver_stop_terminal cell base b output ofs fd bad entered done status run uid
    (receiver_read_trace before)stopped INPUT STOP))as QUIET.
  rewrite ES,receiver_read_trace_app,(QUIET _ _ TAIL),app_nil_r.
  destruct STOP as[le[m[reason[EQ[VALID[LIVE[BUFFER REGS]]]]]]];exact(proj1 BUFFER).
Qed.
