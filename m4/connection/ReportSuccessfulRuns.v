(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.evidence: Restricted witness choices still produce actual unrestricted histories. *)
From Coq Require Import List.
From compcert Require Import Integers Values Memory Events Clight.
Require Import Slice Machine StoreSteps Library LibraryMachine LibraryPreservation Fault WriteMemory WriteAll
  CallContexts WriteCallers ReportingTrace WriteEffects ReportPaths ReportTrace.
Import ListNotations.
Theorem report_allowed_finite_return : forall allow_errors cell P R s,
  report_returns_allow allow_errors cell P R s -> exists events value after,
    library_steps report_ge cell (live s) events (live (Returnstate value Kstop after)) /\
    R (reporting_trace events) value after.
Proof.
  intros allow_errors cell P R s SCRIPT;induction SCRIPT.
  - exists [],value,m;split;[constructor|exact H0].
  - destruct IHSCRIPT as [events [value [after [RUN POST]]]].
    exists (original_event (source_step E0)::events),value,after;split;[|exact POST].
    econstructor;[apply original_step;destruct H0 as [IN [STEP _]];
      exact (Machine.internal report_ge cell s E0 next IN STEP)|exact RUN].
  - destruct IHSCRIPT as [events [value [after [RUN POST]]]].
    destruct (fault_success_after_waits cell m mode name xs ys Kstop 0 H2) as [before [PREFIX _]].
    exists (before++events),value,after;split.
    + eapply library_steps_trans;[|exact RUN]. exact (plug_library_steps _ _ _ _ _ suffix H PREFIX).
    + rewrite reporting_trace_app,(fault_trace_empty _ _ _ _ _ _ _ _ H2 PREFIX);exact POST.
  - subst cell.
    destruct (write_all_success_exists _ _ _ H3) as [before [PREFIX BYTES]].
    assert (POST : report_write_post q input before (Vint Int.zero) m).
    { split;[split;[exact H3|left;auto]|exists [];rewrite BYTES,app_nil_r;reflexivity]. }
    destruct (H6 before (Vint Int.zero) m (tls_history_refl _ _) POST (or_intror eq_refl))
      as [events [value [after [RUN RESULT]]]].
    exists (map original_event before++events),value,after;split.
    + eapply library_steps_trans;[|exact RUN].
      exact (plug_library_steps _ _ _ _ _ suffix H0 (original_runs_preserved _ _ _ _ _ PREFIX)).
    + rewrite reporting_trace_app,reporting_trace_original;exact RESULT.
Qed.
