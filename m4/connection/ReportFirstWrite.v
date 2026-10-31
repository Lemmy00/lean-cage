(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.evidence: A nonempty successful report reaches an actual nonempty write boundary. *)
From Coq Require Import List.
From compcert Require Import Integers Values Memory Events Clight.
Require Import Slice Machine StoreSteps Library LibraryMachine LibraryPreservation Fault WriteMemory WriteAll
  CallContexts WriteCallers ReportingTrace WriteEffects ReportPaths ReportTrace.
Import ListNotations.
Definition report_reaches_write cell s := exists events q input m suffix,
  library_steps report_ge cell (live s) events (live (write_call_initial q suffix m)) /\
  reporting_trace events=[] /\ cell_of q=cell /\ write_owned q input m /\ input<>[] /\ is_call_cont suffix.
Theorem report_first_write_or_return : forall allow_errors cell P R s,
  report_returns_allow allow_errors cell P R s ->
  (exists events value after,
    library_steps report_ge cell (live s) events (live (Returnstate value Kstop after)) /\
    reporting_trace events=[] /\ R [] value after) \/ report_reaches_write cell s.
Proof.
  intros allow_errors cell P R s SCRIPT;induction SCRIPT.
  - left;exists [],value,m;split;[constructor|auto].
  - assert (EDGE : library_step report_ge cell (live s) (original_event (source_step E0)) (live next)).
    { apply original_step;destruct H0 as [IN [STEP _]];exact (Machine.internal report_ge cell s E0 next IN STEP). }
    destruct IHSCRIPT as [[events [value [after [RUN [EMPTY POST]]]]]|[events [q [input [m [suffix [RUN FACTS]]]]]]].
    + left;exists (original_event (source_step E0)::events),value,after;split;[econstructor;eassumption|auto].
    + right;exists (original_event (source_step E0)::events),q,input,m,suffix;split;[econstructor;eassumption|exact FACTS].
  - destruct (fault_success_after_waits cell m mode name xs ys Kstop 0 H2) as [before [PREFIX _]].
    pose proof (fault_trace_empty _ _ _ _ _ _ _ _ H2 PREFIX) as EMPTY.
    pose proof (plug_library_steps _ _ _ _ _ suffix H PREFIX) as CALL.
    destruct IHSCRIPT as [[events [value [after [RUN [EMPTYTAIL POST]]]]]|[events [q [input [after [k [RUN FACTS]]]]]]].
    + left;exists (before++events),value,after;split;[eapply library_steps_trans;eassumption|].
      rewrite reporting_trace_app,EMPTY,EMPTYTAIL;auto.
    + right;exists (before++events),q,input,after,k;split;[eapply library_steps_trans;eassumption|].
      rewrite reporting_trace_app,EMPTY;exact FACTS.
  - destruct input as [|byte rest].
    + subst cell;destruct (write_all_success_exists _ _ _ H3) as [before [PREFIX EMPTY]].
      assert (POST : report_write_post q [] before (Vint Int.zero) m).
      { split;[split;[exact H3|left;auto]|exists [];rewrite EMPTY;reflexivity]. }
      pose proof (plug_library_steps _ _ _ _ _ suffix H0 (original_runs_preserved _ _ _ _ _ PREFIX)) as CALL.
      destruct (H6 before (Vint Int.zero) m (tls_history_refl _ _) POST (or_intror eq_refl))
        as [[events [value [after [RUN [EMPTYTAIL RESULT]]]]]|[events [nextq [input [after [k [RUN FACTS]]]]]]].
      * left;exists (map original_event before++events),value,after;split;[eapply library_steps_trans;eassumption|].
        rewrite reporting_trace_app,reporting_trace_original,EMPTY,EMPTYTAIL;split;[reflexivity|].
        rewrite EMPTY in RESULT;exact RESULT.
      * right;exists (map original_event before++events),nextq,input,after,k;split;[eapply library_steps_trans;eassumption|].
        rewrite reporting_trace_app,reporting_trace_original,EMPTY;exact FACTS.
    + right;exists [],q,(byte::rest),m,suffix;split;[constructor|]. split;[reflexivity|].
      split;[exact H|]. split;[exact H3|]. split;[discriminate|exact H0].
Qed.
