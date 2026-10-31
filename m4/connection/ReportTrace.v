(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.reporting: Relate every returning caller history to its actual emitted bytes. *)
From Coq Require Import List.
From compcert Require Import Integers Values Memory Events Clight.
Require Import Slice Machine Deterministic StoreSteps Library LibraryMachine LibraryPreservation LibraryControl
  Fault WriteMemory WriteAll CallContexts CallEvents CallProgress SourceGuarantees
  WriteCallers ReportingTrace WriteEffects ReportPaths.
Import ListNotations.
Lemma plug_cont_nonstop : forall k suffix,suffix<>Kstop -> plug_cont k suffix<>Kstop.
Proof. intros k suffix NE;destruct k;cbn;congruence. Qed.
Lemma plugged_not_returned : forall s suffix value after,
  suffix<>Kstop -> plug_machine s suffix<>live (Returnstate value Kstop after).
Proof.
  intros [s|m] suffix value after NE EQ;[|discriminate].
  destruct s;cbn in EQ;try discriminate.
  inversion EQ. eapply plug_cont_nonstop;[exact NE|eassumption].
Qed.
Lemma returned_library_history : forall ge cell value m events actual after,
  library_steps ge cell (live (Returnstate value Kstop m)) events (live (Returnstate actual Kstop after)) ->
  events=[] /\ actual=value /\ after=m.
Proof.
  intros ge cell value m events actual after RUN;inversion RUN;subst;[auto|].
  match goal with STEP : library_step _ _ _ _ _ |- _=>
    destruct (control_return_step _ _ _ _ _ _ STEP) as [EV TARGET] end;subst.
  match goal with TAIL : library_steps _ _ (dead _) _ _ |- _=>
    destruct (library_dead_steps _ _ _ _ _ TAIL) as [ES TARGET] end;discriminate.
Qed.
Lemma fault_trace_empty : forall cell m mode name xs ys events target,
  fault_input report_ge m mode name xs ys ->
  library_steps report_ge cell (live (fault_initial name Kstop m)) events target -> reporting_trace events=[].
Proof.
  intros. apply reporting_trace_none;apply selector_reports_nothing.
  exact (fault_events_are_selectors _ _ _ _ _ _ _ actual_fault_symbols H _ _ H0).
Qed.

Theorem report_returns_trace : forall cell P R s,
  report_returns cell P R s -> forall events value after,
  library_steps report_ge cell (live s) events (live (Returnstate value Kstop after)) ->
  R (reporting_trace events) value after.
Proof.
  intros cell P R s SCRIPT;induction SCRIPT;intros events actual final RUN.
  - destruct (returned_library_history _ _ _ _ _ _ _ RUN) as [ES [VALUE MEM]];subst;exact H0.
  - inversion RUN;subst.
    + destruct H0 as [_ [REAL _]];inversion REAL.
    + pose proof H0 as [IN _].
      match goal with STEP : library_step _ _ _ _ _ |- _ =>
        destruct (internal_boundary_unchanged _ _ _ _ _ IN STEP) as [old [EV ORIGINAL]] end;subst.
      destruct (store_edge_cases _ _ _ _ _ _ H0 ORIGINAL) as [[EV TARGET]|[EV TARGET]];subst.
      * cbn [reporting_trace reporting_bytes emitted flat_map app];apply IHSCRIPT;assumption.
      * match goal with TAIL : library_steps _ _ (dead _) _ _ |- _ =>
          destruct (library_dead_steps _ _ _ _ _ TAIL) as [ES TARGET] end;discriminate.
  - destruct (caller_run_decomposition _ _ _ _ _ _ H RUN)
      as [[last [PREFIX SAME]]|[before [rest [value [after [ES [PREFIX TAIL]]]]]]].
    + exfalso;eapply plugged_not_returned;[exact H0|symmetry;exact SAME].
    + pose proof (fault_trace_empty _ _ _ _ _ _ _ _ H2 PREFIX) as EMPTY.
      destruct (fault_return_exact _ _ _ _ _ _ _ _ _ H2 PREFIX) as [VALUE MEM];subst.
      rewrite reporting_trace_app,EMPTY;cbn [app]. apply IHSCRIPT;exact TAIL.
  - subst cell.
    destruct (write_caller_decomposition _ _ _ _ _ _ H3 H0 RUN)
      as [[original [last [ES [SAME [LOCAL [PRESERVED PREFIX]]]]]]|
        [before [rest [value [after [ES [POST [LOCAL TAIL]]]]]]]].
    + exfalso;eapply plugged_not_returned;[exact H1|symmetry;exact SAME].
    + assert (HISTORY : tls_history (cell_of q) m after).
      { exact (write_all_tls_history q input m (map original_event before)
          (live (Returnstate value Kstop after)) H3 (original_runs_preserved _ _ _ _ _ LOCAL)). }
      pose proof (H6 before value after HISTORY (conj POST (proj2 (write_all_prefix_safety q input m before (live (Returnstate value Kstop after)) H3 LOCAL))) (or_introl eq_refl) rest actual final TAIL) as RESULT.
      subst events;rewrite reporting_trace_app,reporting_trace_original;exact RESULT.
Qed.
