(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-receiver.evidence: Whole receiver runs retain arbitrary finite EINTR prefixes and fatal read errors. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Clight.
Require Import Slice IO Machine StoreSteps WriteAll LibraryMachine Fault ResultLayout ProcessEffects
  ReceiverSource ReceiverReadSource ReceiverReadMemory ReceiverRouting ReceiverReadStep
  ReceiverInput ReceiverEntry ReceiverChoice ReceiverConstruction ReceiverReadRuns
  ReceiverTerminalRuns ReceiverTrace ReceiverErrorRuns ReceiverRetries ReceiverRuns.
Import ListNotations.
Open Scope Z_scope.
Definition receiver_retries_observed retries events := exists before rest,
  events=before++rest /\ receiver_error_trace before=repeat(Int.repr 4)retries.
Lemma receiver_error_trace_contains : forall error events,
  In error(receiver_error_trace events) -> receiver_error_observed error events.
Proof.
  intros error events IN;unfold receiver_error_trace in IN;apply in_flat_map in IN;
    destruct IN as[ev[EVENT ERR]].
  destruct ev;cbn in ERR;try contradiction.
  destruct ev;cbn in ERR;try contradiction.
  destruct r;cbn in ERR;try contradiction;destruct ERR as[EQ|FALSE];[|contradiction].
  subst;exists q;exact EVENT.
Qed.
Theorem receiver_complete_retry_run : forall cell base output ofs fd bad entered done status run uid bytes reply waits retries,
  receiver_input cell base output ofs run uid ->(length bytes<=9)%nat ->
  exists b allocated events final,receiver_allocations base b allocated /\
    library_steps result_ge cell(live(receiver_initial output ofs fd bad entered done status Kstop base))events
      (live(Returnstate Vundef Kstop final)) /\
    receiver_read_trace events=bytes /\ receiver_retries_observed retries events /\
    receiver_close_observed fd reply waits events /\
    receiver_choice_result output ofs(receiver_select bytes bad entered done status)uid run b Vundef final.
Proof.
  intros cell base output ofs fd bad entered done status run uid bytes reply waits retries INPUT LIMIT.
  destruct(receiver_entry_prepared cell base output ofs fd bad entered done status run uid INPUT)
    as[b[allocated[initialized[count[ALLOC[PATH[LIVE[BUFFER REGS]]]]]]]].
  destruct(receiver_arbitrary_retries_run retries cell b fd(receiver_temps output ofs fd bad entered done status)bad
    (receiver_live_memory cell base b output ofs fd)[](receiver_first_temps output ofs fd bad entered done status)initialized
    (receiver_live_read _ _ _ _ _ _ (proj1(proj2 INPUT)))(receiver_live_descriptor _ _ _ _ _ _)
    LIVE BUFFER REGS ltac:(cbn;lia))as[retry_events[mid[retry_memory[RETRY[RETRYEMPTY[ERRORS[LIVER[BUFFERR REGSR]]]]]]]].
  destruct(receiver_loop_feed_run cell b fd(receiver_temps output ofs fd bad entered done status)bad
    (receiver_live_memory cell base b output ofs fd)bytes mid retry_memory
    (receiver_live_read _ _ _ _ _ _ (proj1(proj2 INPUT)))(receiver_live_descriptor _ _ _ _ _ _)
    LIVER BUFFERR REGSR LIMIT)as[feed[next[after[FRUN[FTRACE[LIVE'[BUFFER' REGS']]]]]]].
  destruct(receiver_loop_completion_run cell base b output ofs fd bad entered done status run uid bytes next after reply waits
    INPUT LIVE' BUFFER' REGS')as[tail[final[TRUN[EMPTY[CLOSE POST]]]]].
  exists b,allocated,(map original_event(repeat(source_step E0)count)++retry_events++feed++tail),final.
  split;[exact ALLOC|]. split.
  - eapply library_steps_trans;[eapply receiver_source_run;exact PATH|].
    eapply library_steps_trans;[exact RETRY|]. eapply library_steps_trans;eassumption.
  - split.
    + rewrite !receiver_read_trace_app,receiver_read_trace_source,RETRYEMPTY,FTRACE,EMPTY,app_nil_r;reflexivity.
    + split.
      * exists(map original_event(repeat(source_step E0)count)++retry_events),(feed++tail).
        split;[rewrite app_assoc;reflexivity|rewrite receiver_error_trace_app,receiver_error_trace_source,ERRORS;reflexivity].
      * split.
        -- do 3 apply receiver_close_observed_prepend;exact CLOSE.
        -- exact POST.
Qed.
Theorem receiver_complete_error_run : forall cell base output ofs fd bad entered done status run uid bytes error reply waits retries,
  receiver_input cell base output ofs run uid ->(length bytes<9)%nat -> error<>Int.repr 4 ->
  exists b allocated events final,receiver_allocations base b allocated /\
    library_steps result_ge cell(live(receiver_initial output ofs fd bad entered done status Kstop base))events
      (live(Returnstate Vundef Kstop final)) /\
    receiver_read_trace events=bytes /\ receiver_retries_observed retries events /\
    receiver_error_observed error events /\ receiver_close_observed fd reply waits events /\
    receiver_choice_result output ofs(receiver_select bytes Int.one entered done status)uid run b Vundef final.
Proof.
  intros cell base output ofs fd bad entered done status run uid bytes error reply waits retries INPUT SHORT FAILED.
  destruct(receiver_entry_prepared cell base output ofs fd bad entered done status run uid INPUT)
    as[b[allocated[initialized[count[ALLOC[PATH[LIVE[BUFFER REGS]]]]]]]].
  destruct(receiver_arbitrary_retries_run retries cell b fd(receiver_temps output ofs fd bad entered done status)bad
    (receiver_live_memory cell base b output ofs fd)[](receiver_first_temps output ofs fd bad entered done status)initialized
    (receiver_live_read _ _ _ _ _ _ (proj1(proj2 INPUT)))(receiver_live_descriptor _ _ _ _ _ _)
    LIVE BUFFER REGS ltac:(cbn;lia))as[retry_events[mid[retry_memory[RETRY[RETRYEMPTY[ERRORS[LIVER[BUFFERR REGSR]]]]]]]].
  destruct(receiver_loop_feed_run cell b fd(receiver_temps output ofs fd bad entered done status)bad
    (receiver_live_memory cell base b output ofs fd)bytes mid retry_memory
    (receiver_live_read _ _ _ _ _ _ (proj1(proj2 INPUT)))(receiver_live_descriptor _ _ _ _ _ _)
    LIVER BUFFERR REGSR ltac:(lia))as[feed[next[after[FRUN[FTRACE[LIVE'[BUFFER' REGS']]]]]]].
  destruct(receiver_error_stop_run cell b fd(receiver_temps output ofs fd bad entered done status)bad
    (receiver_live_memory cell base b output ofs fd)bytes next after error
    (receiver_live_read _ _ _ _ _ _ (proj1(proj2 INPUT)))(receiver_live_descriptor _ _ _ _ _ _)
    LIVE' BUFFER' REGS' SHORT FAILED)as[err_events[stopped[err_memory[ERUN[EEMPTY[ETRACE[LIVEE[BUFFERE[KEEP[BAD USED]]]]]]]]]].
  destruct(receiver_terminal_run cell base b bytes fd Int.one entered done status stopped err_memory output ofs run uid reply waits
    INPUT LIVEE BUFFERE ltac:(rewrite(KEEP __res ltac:(cbn;tauto));unfold receiver_temps;WriteAll.lookup)
    BAD ltac:(rewrite(KEEP _entered ltac:(cbn;tauto));unfold receiver_temps;WriteAll.lookup)
    ltac:(rewrite(KEEP _leader_done ltac:(cbn;tauto));unfold receiver_temps;WriteAll.lookup)
    ltac:(rewrite(KEEP _leader_status ltac:(cbn;tauto));unfold receiver_temps;WriteAll.lookup)USED)
    as[tail[final[TRUN[EMPTY[CLOSE POST]]]]].
  exists b,allocated,(map original_event(repeat(source_step E0)count)++retry_events++feed++err_events++tail),final.
  split;[exact ALLOC|]. split.
  - eapply library_steps_trans;[eapply receiver_source_run;exact PATH|].
    eapply library_steps_trans;[exact RETRY|]. eapply library_steps_trans;[exact FRUN|].
    eapply library_steps_trans;eassumption.
  - split.
    + rewrite !receiver_read_trace_app,receiver_read_trace_source,RETRYEMPTY,FTRACE,EEMPTY,EMPTY,app_nil_r;reflexivity.
    + split.
      * exists(map original_event(repeat(source_step E0)count)++retry_events),(feed++err_events++tail).
        split;[rewrite app_assoc;reflexivity|rewrite receiver_error_trace_app,receiver_error_trace_source,ERRORS;reflexivity].
      * split.
        -- do 3 apply receiver_error_observed_prepend;apply receiver_error_observed_append.
           apply receiver_error_trace_contains;rewrite ETRACE;left;reflexivity.
        -- split;[do 4 apply receiver_close_observed_prepend;exact CLOSE|exact POST].
Qed.
