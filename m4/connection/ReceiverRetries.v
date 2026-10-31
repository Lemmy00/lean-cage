(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-receiver.reads: EINTR retries and non-EINTR failures follow the actual TLS branch. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Clight.
Require Import Slice IO Machine ClightSteps StoreSteps WriteAll LibraryMachine Fault ResultLayout
  ReceiverSource ReceiverReadSource ReceiverReadMemory ReceiverRouting ReceiverReadStep
  ReceiverReadReturns ReceiverReadRuns ReceiverErrorRuns ReceiverTrace.
Import ListNotations.
Open Scope Z_scope.
Theorem receiver_retry_once_run : forall cell b fd original bad P bytes le m ,
  receiver_reads_preserve cell b fd P -> receiver_descriptor b fd P -> P m ->
  receiver_buffer cell b m bytes -> receiver_registers original bad bytes le ->(length bytes<9)%nat ->
  exists events next after,
    library_steps result_ge cell(live(receiver_loop_state b le Kstop m))events
      (live(receiver_loop_state b next Kstop after)) /\ receiver_read_trace events=[] /\
    receiver_error_trace events=[(Int.repr 4)] /\ P after /\ receiver_buffer cell b after bytes /\
    receiver_registers original bad bytes next.
Proof.
  intros cell b fd original bad P bytes le m  PRESERVE DESCRIPTOR PM BUFFER REGS SHORT .
  destruct(receiver_error_address_run cell b fd original bad P bytes le m (Int.repr 4)
    PRESERVE DESCRIPTOR PM BUFFER REGS SHORT)as[before[after[RUN[EMPTY[ERRORS[PA[BUFFER'[REGS'[N LOAD]]]]]]]]].
  destruct REGS' as[KEEP[BAD USED]].
  destruct(receiver_errno_retry_to_loop b cell(receiver_failed_temps le fd (Int.repr 4))Kstop after(Z.of_nat(length bytes)) USED N LOAD)
    as[count[next[KEPT[BAD'[USED' PATH]]]]].
  exists(before++map original_event(repeat(source_step E0)count)),next,after;split.
  - eapply library_steps_trans;[exact RUN|eapply receiver_source_run;exact PATH].
  - split;[rewrite receiver_read_trace_app,EMPTY,receiver_read_trace_source;reflexivity|].
    split;[rewrite receiver_error_trace_app,ERRORS,receiver_error_trace_source;reflexivity|].
    split;[exact PA|]. split;[exact BUFFER'|]. split;[eapply receiver_kept_trans;eassumption|].
    split;[rewrite BAD';exact BAD|exact USED'].
Qed.

Theorem receiver_error_stop_run : forall cell b fd original bad P bytes le m error,
  receiver_reads_preserve cell b fd P -> receiver_descriptor b fd P -> P m ->
  receiver_buffer cell b m bytes -> receiver_registers original bad bytes le ->(length bytes<9)%nat -> error<>Int.repr 4 ->
  exists events next after,
    library_steps result_ge cell(live(receiver_loop_state b le Kstop m))events
      (live(receiver_closed_state b next Kstop after)) /\ receiver_read_trace events=[] /\
    receiver_error_trace events=[error] /\ P after /\ receiver_buffer cell b after bytes /\
    receiver_registers original Int.one bytes next.
Proof.
  intros cell b fd original bad P bytes le m error PRESERVE DESCRIPTOR PM BUFFER REGS SHORT NOTRETRY.
  destruct(receiver_error_address_run cell b fd original bad P bytes le m error
    PRESERVE DESCRIPTOR PM BUFFER REGS SHORT)as[before[after[RUN[EMPTY[ERRORS[PA[BUFFER'[REGS'[N LOAD]]]]]]]]].
  destruct REGS' as[KEEP[BAD USED]].
  destruct(receiver_errno_failure_to_close b cell(receiver_failed_temps le fd error)Kstop after(Z.of_nat(length bytes)) error USED N NOTRETRY LOAD)
    as[count[next[KEPT[BAD'[USED' PATH]]]]].
  exists(before++map original_event(repeat(source_step E0)count)),next,after;split.
  - eapply library_steps_trans;[exact RUN|eapply receiver_source_run;exact PATH].
  - split;[rewrite receiver_read_trace_app,EMPTY,receiver_read_trace_source;reflexivity|].
    split;[rewrite receiver_error_trace_app,ERRORS,receiver_error_trace_source;reflexivity|].
    split;[exact PA|]. split;[exact BUFFER'|]. split;[eapply receiver_kept_trans;eassumption|].
    split;[exact BAD'|exact USED'].
Qed.

Theorem receiver_arbitrary_retries_run : forall retries cell b fd original bad P bytes le m,
  receiver_reads_preserve cell b fd P -> receiver_descriptor b fd P -> P m ->
  receiver_buffer cell b m bytes -> receiver_registers original bad bytes le ->(length bytes<9)%nat ->
  exists events next after,
    library_steps result_ge cell(live(receiver_loop_state b le Kstop m))events
      (live(receiver_loop_state b next Kstop after)) /\ receiver_read_trace events=[] /\
    receiver_error_trace events=repeat(Int.repr 4)retries /\ P after /\ receiver_buffer cell b after bytes /\
    receiver_registers original bad bytes next.
Proof.
  intros retries cell b fd original bad P bytes;induction retries as[|retries IH];
    intros le m PRESERVE DESCRIPTOR PM BUFFER REGS SHORT.
  - exists [],le,m;split;[constructor|]. split;[reflexivity|]. split;[reflexivity|].
    split;[exact PM|]. split;assumption.
  - destruct(receiver_retry_once_run cell b fd original bad P bytes le m PRESERVE DESCRIPTOR PM BUFFER REGS SHORT)
      as[first[mid[before[RUN[EMPTY[ERRORS[PB[BUFFER' REGS']]]]]]]].
    destruct(IH mid before PRESERVE DESCRIPTOR PB BUFFER' REGS' SHORT)
      as[rest[next[after[TAIL[EMPTY'[ERRORS'[PA[BUFFER'' REGS'']]]]]]]].
    exists(first++rest),next,after;split;[eapply library_steps_trans;eassumption|].
    split;[rewrite receiver_read_trace_app,EMPTY,EMPTY';reflexivity|].
    split;[rewrite receiver_error_trace_app,ERRORS,ERRORS';reflexivity|].
    split;[exact PA|]. split;assumption.
Qed.
