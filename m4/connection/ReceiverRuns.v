(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-receiver.evidence: Actual whole-receiver executions for every bounded input and any close reply. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Clight.
Require Import Slice IO Machine StoreSteps WriteAll LibraryMachine Fault ResultLayout ProcessEffects
  ReceiverSource ReceiverReadSource ReceiverReadMemory ReceiverRouting ReceiverReadStep
  ReceiverInput ReceiverEntry ReceiverChoice ReceiverConstruction ReceiverReadRuns
  ReceiverTerminalRuns ReceiverTrace.
Import ListNotations.
Open Scope Z_scope.
Theorem receiver_loop_completion_run : forall cell base b output ofs fd bad entered done status run uid bytes le m reply waits,
  receiver_input cell base output ofs run uid -> receiver_live_memory cell base b output ofs fd m ->
  receiver_buffer cell b m bytes ->
  receiver_registers(receiver_temps output ofs fd bad entered done status)bad bytes le ->
  exists events final,
    library_steps result_ge cell(live(receiver_loop_state b le Kstop m))events(live(Returnstate Vundef Kstop final)) /\
    receiver_read_trace events=[] /\ receiver_close_observed fd reply waits events /\
    receiver_choice_result output ofs(receiver_select bytes bad entered done status)uid run b Vundef final.
Proof.
  intros cell base b output ofs fd bad entered done status run uid bytes le m reply waits INPUT LIVE BUFFER REGS.
  destruct(receiver_loop_stop_run cell b fd(receiver_temps output ofs fd bad entered done status)bad bytes le m
    BUFFER REGS(proj2(proj2(proj2 LIVE))))as[before[next[reason[RUN[EMPTY[STOP[SAME[KEEP[BAD USED]]]]]]]]].
  destruct(receiver_terminal_run cell base b bytes fd bad entered done status next m output ofs run uid reply waits
    INPUT LIVE BUFFER ltac:(rewrite(KEEP __res ltac:(cbn;tauto));unfold receiver_temps;WriteAll.lookup)
    BAD ltac:(rewrite(KEEP _entered ltac:(cbn;tauto));unfold receiver_temps;WriteAll.lookup)
    ltac:(rewrite(KEEP _leader_done ltac:(cbn;tauto));unfold receiver_temps;WriteAll.lookup)
    ltac:(rewrite(KEEP _leader_status ltac:(cbn;tauto));unfold receiver_temps;WriteAll.lookup)USED)
    as[after[final[TAIL[EMPTY'[CLOSE POST]]]]].
  exists(before++after),final;split;[eapply library_steps_trans;eassumption|].
  split;[rewrite receiver_read_trace_app,EMPTY,EMPTY';reflexivity|].
  split;[apply receiver_close_observed_prepend;exact CLOSE|exact POST].
Qed.
Theorem receiver_complete_run : forall cell base output ofs fd bad entered done status run uid bytes reply waits,
  receiver_input cell base output ofs run uid ->(length bytes<=9)%nat ->
  exists b allocated events final,receiver_allocations base b allocated /\
    library_steps result_ge cell(live(receiver_initial output ofs fd bad entered done status Kstop base))events
      (live(Returnstate Vundef Kstop final)) /\
    receiver_read_trace events=bytes /\ receiver_close_observed fd reply waits events /\
    receiver_choice_result output ofs(receiver_select bytes bad entered done status)uid run b Vundef final.
Proof.
  intros cell base output ofs fd bad entered done status run uid bytes reply waits INPUT LIMIT.
  destruct(receiver_entry_prepared cell base output ofs fd bad entered done status run uid INPUT)
    as[b[allocated[initialized[count[ALLOC[PATH[LIVE[BUFFER REGS]]]]]]]].
  assert(FEED : exists events next after,
    library_steps result_ge cell(live(receiver_loop_state b(receiver_first_temps output ofs fd bad entered done status)Kstop initialized))events
      (live(receiver_loop_state b next Kstop after)) /\
    receiver_read_trace events=bytes /\ receiver_live_memory cell base b output ofs fd after /\
    receiver_buffer cell b after bytes /\
    receiver_registers(receiver_temps output ofs fd bad entered done status)bad bytes next).
  { destruct bytes as[|first rest].
    - exists [],(receiver_first_temps output ofs fd bad entered done status),initialized.
      split;[constructor|]. split;[reflexivity|]. split;[exact LIVE|]. split;assumption.
    - eapply receiver_loop_transfer_run with(prefix:=[]);
      [apply receiver_live_read;exact(proj1(proj2 INPUT))|apply receiver_live_descriptor|exact LIVE|exact BUFFER|exact REGS|cbn in *;lia]. }
  destruct FEED as[feed[next[after[FRUN[FTRACE[LIVE'[BUFFER' REGS']]]]]]].
  destruct(receiver_loop_completion_run cell base b output ofs fd bad entered done status run uid bytes next after reply waits
    INPUT LIVE' BUFFER' REGS')as[tail[final[TRUN[EMPTY[CLOSE POST]]]]].
  exists b,allocated,(map original_event(repeat(source_step E0)count)++feed++tail),final.
  split;[exact ALLOC|]. split.
  - eapply library_steps_trans;[eapply receiver_source_run;exact PATH|]. eapply library_steps_trans;eassumption.
  - split.
    + rewrite !receiver_read_trace_app,receiver_read_trace_source,FTRACE,EMPTY,app_nil_r;reflexivity.
    + split;[apply receiver_close_observed_prepend;apply receiver_close_observed_prepend;exact CLOSE|exact POST].
Qed.
