(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.reporting: Prefixes before publication contribute no report bytes. *)
From Coq Require Import List.
From compcert Require Import Integers Values Memory Clight.
Require Import Machine StoreSteps Library LibraryMachine LibraryPreservation LibraryControl
  CallPaths ReportingTrace CopyPaths CopyTrace.
Import ListNotations.
Theorem copy_reaches_consequence : forall ge (P Q : mem -> Prop) A B s,
  copy_reaches ge P A s -> (forall m,P m -> Q m) -> (forall last,A last -> B last) ->
  copy_reaches ge Q B s.
Proof.
  intros ge P Q A B s PATH;induction PATH;intros MEMORY POST.
  - apply copy_reaches_done;[apply MEMORY;exact H|apply POST;exact H0].
  - eapply copy_reaches_source;[apply MEMORY;exact H|exact H0|apply IHPATH;assumption].
  - eapply copy_reaches_call;[apply MEMORY;exact H|exact H0| |].
    + intros;apply MEMORY;eapply H1;eassumption.
    + intros;apply H3;assumption.
Qed.
Theorem copy_reaches_return_trace : forall ge cell P Q s (R : list Byte.int -> val -> mem -> Prop),
  copy_reaches ge P Q s ->
  (forall last,Q last -> forall events value after,
    library_steps ge cell (live last) events (live (Returnstate value Kstop after)) ->
    R (reporting_trace events) value after) ->
  forall events value after,library_steps ge cell (live s) events (live (Returnstate value Kstop after)) ->
    R (reporting_trace events) value after.
Proof.
  intros ge cell P Q s R PATH;induction PATH;intros LAST events value final RUN.
  - eapply LAST;[exact H0|exact RUN].
  - inversion RUN;subst.
    + destruct H0 as [_ [REAL _]];inversion REAL.
    + pose proof H0 as [IN _].
      match goal with STEP : library_step _ _ _ _ _ |- _=>
        destruct (internal_boundary_unchanged _ _ _ _ _ IN STEP) as [old [EV ORIGINAL]] end;subst.
      destruct (store_edge_cases _ _ _ _ _ _ H0 ORIGINAL) as [[EV TARGET]|[EV TARGET]];subst.
      * cbn [reporting_trace reporting_bytes WriteAll.emitted flat_map app];eapply IHPATH;[exact LAST|eassumption].
      * match goal with TAIL : library_steps _ _ (dead _) _ _ |- _=>
          destruct (library_dead_steps _ _ _ _ _ TAIL) as [ES TARGET] end;discriminate.
  - destruct (memcpy_run_cases _ _ _ _ _ _ _ _ _ H0 RUN)
      as [[n [ES TARGET]]|[[n [ES TARGET]]|[[n [schedule [after [PART [ES TARGET]]]]]|[n [after [rest [RESULT [ES AFTER]]]]]]]];
      try discriminate.
    subst events;rewrite reporting_trace_app,waiting_reports_nothing.
    cbn [reporting_trace reporting_bytes flat_map app];eapply H3;[exact RESULT|exact LAST|exact AFTER].
Qed.
