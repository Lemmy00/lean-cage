(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.reporting: Encoding and interrupted copies emit no report bytes. *)
From Coq Require Import List.
From compcert Require Import Values Memory Events Clight.
Require Import Machine StoreSteps Library LibraryMachine LibraryPreservation LibraryControl
  SourceReach ReportingTrace CopyPaths.
Import ListNotations.
Lemma waiting_reports_nothing : forall n, reporting_trace (repeat library_wait n)=[].
Proof. induction n;cbn;auto. Qed.
Theorem copy_reaches_reports_prefix : forall ge cell P Q s bytes,
  copy_reaches ge P Q s ->
  (forall last,Q last -> reports_prefix ge cell last bytes) -> reports_prefix ge cell s bytes.
Proof.
  intros ge cell P Q s bytes PATH;induction PATH;intros LAST.
  - apply LAST;exact H0.
  - eapply source_path_reports_prefix.
    + eapply store_next;[exact H|exact H0|]. constructor;inversion PATH;assumption.
    + apply IHPATH;exact LAST.
  - intros events target RUN.
    destruct (memcpy_run_cases _ _ _ _ _ _ _ _ _ H0 RUN)
      as [[n [ES TARGET]]|[[n [ES TARGET]]|[[n [schedule [after [PART [ES TARGET]]]]]|[n [after [rest [RESULT [ES AFTER]]]]]]]];
      subst events.
    + rewrite waiting_reports_nothing;exists bytes;reflexivity.
    + rewrite reporting_trace_app,waiting_reports_nothing;exists bytes;reflexivity.
    + rewrite reporting_trace_app,waiting_reports_nothing;exists bytes;reflexivity.
    + rewrite reporting_trace_app,waiting_reports_nothing.
      cbn [reporting_trace reporting_bytes flat_map app].
      exact (H3 after RESULT LAST _ _ AFTER).
Qed.

Theorem copy_reaches_quiet_run : forall ge cell P Q s,
  copy_reaches ge P Q s -> exists events last,
    library_steps ge cell (live s) events (live last) /\ Forall control_progress events /\
    reporting_trace events=[] /\ Q last.
Proof.
  intros ge cell P Q s PATH;induction PATH.
  - exists [],s;split;[constructor|]. split;[constructor|]. split;[reflexivity|exact H0].
  - destruct IHPATH as [events [last [RUN [PROGRESS [EMPTY POST]]]]].
    exists (original_event (source_step E0)::events),last.
    split;[eapply library_steps_cons;[apply original_step;destruct H0 as [IN [STEP _]];
      exact (Machine.internal ge cell s E0 next IN STEP)|exact RUN]|].
    split;[constructor;[unfold control_progress;cbn;repeat split;discriminate|exact PROGRESS]|].
    split;[exact EMPTY|exact POST].
  - destruct (copy_progress _ _ _ _ H0) as [after RESULT].
    destruct (H3 _ RESULT) as [events [last [RUN [PROGRESS [EMPTY POST]]]]].
    exists (memcpy_returned source destination bytes::events),last.
    split;[econstructor;[apply memcpy_step;exact RESULT|exact RUN]|].
    split;[constructor;[unfold control_progress;cbn;repeat split;discriminate|exact PROGRESS]|].
    split;[exact EMPTY|exact POST].
Qed.
