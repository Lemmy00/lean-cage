(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.evidence: Real failed-write histories inhabit unrestricted source certificates. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers Values Memory Events Clight.
Require Import Slice IO Machine Library LibraryMachine LibraryPreservation LibraryControl Fault WriteMemory WriteAll
  WriteWitnesses WriteCallers CallContexts ReportingTrace WriteEffects ReportPaths ReportTrace.
Import ListNotations.
Open Scope Z_scope.
Definition reply_bytes r := match r with transfer bytes _=>bytes|_=>[] end.
Lemma live_steps_emitted_replies : forall ge cell start events target,
  steps ge cell start events target -> forall final,target=live final ->
  emitted_trace events=flat_map reply_bytes (replies events).
Proof.
  intros ge cell start events target RUN;induction RUN;intros final EQ;subst.
  - reflexivity.
  - specialize (IHRUN final eq_refl). destruct e.
    + exact IHRUN.
    + change (reply_bytes r++emitted_trace rest=reply_bytes r++flat_map reply_bytes (replies rest)).
      rewrite IHRUN;reflexivity.
    + exact IHRUN.
    + exact IHRUN.
    + exact IHRUN.
    + inversion H;subst.
      destruct (library_dead_steps _ _ _ _ _ (original_runs_preserved _ _ _ _ _ RUN)) as [ES TARGET];discriminate.
Qed.
Theorem write_empty_report_return : forall q input m error,
  write_owned q input m -> error<>Int.repr 4 ->
  exists events value after,
    steps (Clight.globalenv Slice.prog) (cell_of q) (live (initial_state q m)) events
      (live (Returnstate value Kstop after)) /\
    emitted_trace events=[] /\ tls_history (cell_of q) m after /\ report_write_post q input events value after.
Proof.
  intros q input m error OWN ERROR.
  assert (CHOOSE : exists events value after,
    steps (Clight.globalenv Slice.prog) (cell_of q) (live (initial_state q m)) events
      (live (Returnstate value Kstop after)) /\ emitted_trace events=[]).
  { destruct input as [|byte rest].
    - destruct (write_all_success_exists _ _ _ OWN) as [events [RUN BYTES]].
      exists events,(Vint Int.zero),m;auto.
    - destruct (source_error_return q (byte::rest) m error OWN ltac:(discriminate) ERROR)
        as [events [after [RUN REPLIES]]].
      exists events,(Vint Int.mone),after;split;[exact RUN|].
      rewrite (live_steps_emitted_replies _ _ _ _ _ RUN _ eq_refl),REPLIES;reflexivity. }
  destruct CHOOSE as [events [value [after [RUN EMPTY]]]].
  exists events,value,after;split;[exact RUN|]. split;[exact EMPTY|]. split.
  - exact (write_all_tls_history q input m (map original_event events) (live (Returnstate value Kstop after))
      OWN (original_runs_preserved _ _ _ _ _ RUN)).
  - split;[split;[exact (proj1 (write_all_prefix_safety _ _ _ _ _ OWN RUN))|
      exact (write_all_return_exact _ _ _ _ _ _ OWN RUN)]|].
    exact (proj2 (write_all_prefix_safety _ _ _ _ _ OWN RUN)).
Qed.
Theorem report_empty_finite_return : forall cell P R s error,
  report_returns cell P R s -> error<>Int.repr 4 -> exists events value after,
    library_steps report_ge cell (live s) events (live (Returnstate value Kstop after)) /\
    reporting_trace events=[] /\ R [] value after.
Proof.
  intros cell P R s error SCRIPT ERROR;induction SCRIPT.
  - exists [],value,m;split;[constructor|auto].
  - destruct IHSCRIPT as [events [value [after [RUN [EMPTY POST]]]]].
    exists (original_event (source_step E0)::events),value,after;split;[|split;assumption].
    econstructor;[apply original_step;destruct H0 as [IN [STEP _]];
      exact (Machine.internal report_ge cell s E0 next IN STEP)|exact RUN].
  - destruct IHSCRIPT as [events [value [after [RUN [EMPTY POST]]]]].
    destruct (fault_success_after_waits cell m mode name xs ys Kstop 0 H2) as [before [PREFIX _]].
    exists (before++events),value,after;split.
    + eapply library_steps_trans;[|exact RUN]. exact (plug_library_steps _ _ _ _ _ suffix H PREFIX).
    + rewrite reporting_trace_app,(fault_trace_empty _ _ _ _ _ _ _ _ H2 PREFIX);auto.
  - subst cell.
    destruct (write_empty_report_return q input m error H3 ERROR) as [before [value [after [PREFIX [EMPTY [HISTORY POST]]]]]].
    destruct (H6 before value after HISTORY POST (or_introl eq_refl)) as [events [final [last [RUN [EMPTYTAIL RESULT]]]]].
    exists (map original_event before++events),final,last;split.
    + eapply library_steps_trans;[|exact RUN].
      exact (plug_library_steps _ _ _ _ _ suffix H0 (original_runs_preserved _ _ _ _ _ PREFIX)).
    + rewrite reporting_trace_app,reporting_trace_original,EMPTY,EMPTYTAIL;split;[reflexivity|].
      rewrite EMPTY in RESULT;exact RESULT.
Qed.
