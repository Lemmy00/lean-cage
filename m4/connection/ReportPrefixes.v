(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.reporting: Bound every emitted prefix, including interrupted transfers. *)
From Coq Require Import List.
From compcert Require Import Integers Values Memory Events Clight.
Require Import Slice Machine StoreSteps Library LibraryMachine LibraryPreservation LibraryControl
  Fault WriteMemory WriteAll CallContexts WriteCallers ReportingTrace WriteEffects
  ReportPaths ReportTrace ReportRuns.
Import ListNotations.
Lemma returned_trace_empty : forall ge cell value m events target,
  library_steps ge cell (live (Returnstate value Kstop m)) events target -> reporting_trace events=[].
Proof.
  intros ge cell value m events target RUN;inversion RUN;subst;[reflexivity|].
  match goal with STEP : library_step _ _ _ _ _ |- _=>
    destruct (control_return_step _ _ _ _ _ _ STEP) as [EV TARGET] end;subst.
  match goal with TAIL : library_steps _ _ (dead _) _ _ |- _=>
    destruct (library_dead_steps _ _ _ _ _ TAIL) as [ES TARGET] end;subst;reflexivity.
Qed.
Theorem report_returns_prefix : forall cell P R s,
  report_returns cell P R s -> forall expected acc,
  (forall bytes value after,R bytes value after -> exists rest,expected=acc++bytes++rest) ->
  forall events target,library_steps report_ge cell (live s) events target ->
    exists rest,expected=acc++reporting_trace events++rest.
Proof.
  intros cell P R s SCRIPT;induction SCRIPT;intros expected acc BOUND events target RUN.
  - rewrite (returned_trace_empty _ _ _ _ _ _ RUN);exact (BOUND [] value m H0).
  - inversion RUN;subst.
    + exact (IHSCRIPT expected acc BOUND [] (live next) (library_steps_nil _ _ _)).
    + pose proof H0 as [IN _].
      match goal with STEP : library_step _ _ _ _ _ |- _=>
        destruct (internal_boundary_unchanged _ _ _ _ _ IN STEP) as [old [EV ORIGINAL]] end;subst.
      destruct (store_edge_cases _ _ _ _ _ _ H0 ORIGINAL) as [[EV TARGET]|[EV TARGET]];subst.
      * cbn [reporting_trace reporting_bytes emitted flat_map app];eapply IHSCRIPT;[exact BOUND|eassumption].
      * match goal with TAIL : library_steps _ _ (dead _) _ _ |- _=>
          destruct (library_dead_steps _ _ _ _ _ TAIL) as [ES TARGET] end;subst.
        exact (IHSCRIPT expected acc BOUND [] (live next) (library_steps_nil _ _ _)).
  - destruct (caller_run_decomposition _ _ _ _ _ _ H RUN)
      as [[last [PREFIX SAME]]|[before [rest [value [after [ES [PREFIX TAIL]]]]]]].
    + rewrite (fault_trace_empty _ _ _ _ _ _ _ _ H2 PREFIX).
      exact (IHSCRIPT expected acc BOUND [] (live (Returnstate (fault_value xs ys) suffix m)) (library_steps_nil _ _ _)).
    + pose proof (fault_trace_empty _ _ _ _ _ _ _ _ H2 PREFIX) as EMPTY.
      destruct (fault_return_exact _ _ _ _ _ _ _ _ _ H2 PREFIX) as [VALUE MEM];subst.
      rewrite reporting_trace_app,EMPTY;cbn [app]. eapply IHSCRIPT;[exact BOUND|exact TAIL].
  - subst cell.
    destruct (write_caller_decomposition _ _ _ _ _ _ H3 H0 RUN)
      as [[original [last [ES [SAME [LOCAL [PRESERVED [remaining PREFIX]]]]]]]|
        [before [rest [value [after [ES [POST [LOCAL TAIL]]]]]]]].
    + destruct (write_all_success_exists _ _ _ H3) as [success [SUCCESS COMPLETE]].
      assert (POST : report_write_post q input success (Vint Int.zero) m).
      { split;[split;[exact H3|left;auto]|exists [];rewrite COMPLETE,app_nil_r;reflexivity]. }
      destruct (report_returns_run _ _ _ _ (H5 success (Vint Int.zero) m (tls_history_refl _ _) POST (or_introl eq_refl)))
        as [future [value [after [FUTURE RESULT]]]].
      destruct (BOUND _ _ _ RESULT) as [tail EQ]. rewrite COMPLETE,PREFIX in EQ.
      subst events;rewrite reporting_trace_original.
      exists (remaining++reporting_trace future++tail);rewrite <- !app_assoc in *;exact EQ.
    + assert (HISTORY : tls_history (cell_of q) m after).
      { exact (write_all_tls_history q input m (map original_event before)
          (live (Returnstate value Kstop after)) H3 (original_runs_preserved _ _ _ _ _ LOCAL)). }
      specialize (H6 before value after HISTORY (conj POST (proj2 (write_all_prefix_safety q input m before (live (Returnstate value Kstop after)) H3 LOCAL))) (or_introl eq_refl) expected (acc++emitted_trace before)).
      assert (NEXTBOUND : forall bytes v final,
        R (emitted_trace before++bytes) v final -> exists tail,expected=(acc++emitted_trace before)++bytes++tail).
      { intros bytes v final POSTCONDITION;destruct (BOUND _ _ _ POSTCONDITION) as [tail EQ].
        exists tail;rewrite <- !app_assoc in *;exact EQ. }
      destruct (H6 NEXTBOUND _ _ TAIL) as [tail EQ]. subst events.
      rewrite reporting_trace_app,reporting_trace_original;exists tail;rewrite <- !app_assoc in *;exact EQ.
Qed.
