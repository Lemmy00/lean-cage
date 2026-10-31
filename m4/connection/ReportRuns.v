(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.evidence: Every constructed caller certificate has an actual finite return. *)
From Coq Require Import List.
From compcert Require Import Integers Values Memory Events Clight.
Require Import Slice Machine StoreSteps Library LibraryMachine Fault WriteMemory WriteAll
  CallContexts WriteCallers ReportingTrace WriteEffects ReportPaths ReportTrace.
Import ListNotations.
Theorem report_returns_some_return : forall cell P R s,
  report_returns cell P R s -> exists events value after,
    library_steps report_ge cell (live s) events (live (Returnstate value Kstop after)).
Proof.
  intros cell P R s SCRIPT;induction SCRIPT.
  - exists [],value,m;constructor.
  - destruct IHSCRIPT as [events [value [after RUN]]].
    exists (original_event (source_step E0)::events),value,after.
    econstructor;[apply original_step;destruct H0 as [IN [STEP _]];
      exact (Machine.internal report_ge cell s E0 next IN STEP)|exact RUN].
  - destruct IHSCRIPT as [events [value [after RUN]]].
    destruct (fault_success_after_waits cell m mode name xs ys Kstop 0 H2) as [before [PREFIX _]].
    exists (before++events),value,after;eapply library_steps_trans;[|exact RUN].
    exact (plug_library_steps _ _ _ _ _ suffix H PREFIX).
  - subst cell.
    destruct (write_all_success_exists _ _ _ H3) as [before [PREFIX BYTES]].
    assert (POST : report_write_post q input before (Vint Int.zero) m).
    { split;[split;[exact H3|left;auto]|exists [];rewrite BYTES,app_nil_r;reflexivity]. }
    destruct (H6 before (Vint Int.zero) m (tls_history_refl _ _) POST (or_introl eq_refl)) as [events [value [after RUN]]].
    exists (map original_event before++events),value,after;eapply library_steps_trans;[|exact RUN].
    exact (plug_library_steps _ _ _ _ _ suffix H0 (original_runs_preserved _ _ _ _ _ PREFIX)).
Qed.
Theorem report_returns_run : forall cell P R s,
  report_returns cell P R s -> exists events value after,
    library_steps report_ge cell (live s) events (live (Returnstate value Kstop after)) /\
    R (reporting_trace events) value after.
Proof.
  intros cell P R s SCRIPT;destruct (report_returns_some_return _ _ _ _ SCRIPT) as [events [value [after RUN]]].
  exists events,value,after;split;[exact RUN|eapply report_returns_trace;[exact SCRIPT|exact RUN]].
Qed.
