(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.reporting: Finite caller certificates compose real selectors and whole writes. *)
From Coq Require Import List.
From compcert Require Import Integers Values Memory Clight.
Require Import Slice IO Machine Deterministic StoreSteps Library LibraryMachine LibraryControl
  Fault WriteMemory WriteAll CallContexts CallProgress SourcePaths SourceGuarantees
  WriteCallers ReportingTrace ProcedureCalls WriteEffects WriteGuarantees.
Import ListNotations.
Definition report_ge := Clight.globalenv Slice.prog.
Definition report_write_post q input events value after :=
  write_return_post q input events value after /\ exists rest,input=emitted_trace events++rest.
Inductive report_returns_allow (allow_errors : bool) cell (P : mem -> Prop) : (list Byte.int -> val -> mem -> Prop) -> Clight.state -> Prop :=
| report_returns_done : forall R value m,
    P m -> R [] value m -> report_returns_allow allow_errors cell P R (Returnstate value Kstop m)
| report_returns_source : forall R s next,
    P (memory_of s) -> store_edge report_ge s next ->
    report_returns_allow allow_errors cell P R next -> report_returns_allow allow_errors cell P R s
| report_returns_selector : forall R m mode name xs ys suffix,
    is_call_cont suffix -> suffix<>Kstop -> P m -> fault_input report_ge m mode name xs ys ->
    report_returns_allow allow_errors cell P R (Returnstate (fault_value xs ys) suffix m) ->
    report_returns_allow allow_errors cell P R (plug_state (fault_initial name Kstop m) suffix)
| report_returns_write : forall R q input m suffix,
    cell_of q=cell -> is_call_cont suffix -> suffix<>Kstop ->
    P m -> write_owned q input m ->
    (forall after,tls_history cell m after -> P after) ->
    (forall events value after,tls_history cell m after -> report_write_post q input events value after ->
      (allow_errors=true \/ value=Vint Int.zero) ->
      report_returns_allow allow_errors cell P (fun more final last=>R (emitted_trace events++more) final last)
        (Returnstate value suffix after)) ->
    report_returns_allow allow_errors cell P R (write_call_initial q suffix m).

Definition report_returns := report_returns_allow true.

Lemma report_returns_memory : forall allow_errors cell P R s,report_returns_allow allow_errors cell P R s -> P (memory_of s).
Proof. intros;inversion H;subst;cbn;assumption. Qed.
Lemma report_returns_path : forall allow_errors cell P R s count next,
  store_path report_ge P s count next -> report_returns_allow allow_errors cell P R next -> report_returns_allow allow_errors cell P R s.
Proof. intros allow_errors cell P R s count next PATH;induction PATH;intros NEXT;[exact NEXT|eapply report_returns_source;eauto]. Qed.

Lemma procedure_guarantee_post : forall ge cell P A B s,
  procedure_guarantee ge cell P A s -> (forall value after,A value after -> B value after) ->
  procedure_guarantee ge cell P B s.
Proof.
  intros ge cell P A B s [MEMORY PROGRESS] POST;split;[exact MEMORY|].
  intros events current RUN;destruct (PROGRESS _ _ RUN) as [[value [after [EQ RESULT]]]|NEXT];[left|right;exact NEXT].
  exists value,after;split;[exact EQ|apply POST;exact RESULT].
Qed.

Theorem report_returns_guarantee : forall cell P R s,
  report_returns cell P R s ->
  procedure_guarantee report_ge cell P (fun value after=>exists bytes,R bytes value after) s.
Proof.
  intros cell P R s SCRIPT;induction SCRIPT.
  - apply source_returns_guarantee;apply source_returns_done;[exact H|exists [];exact H0].
  - eapply source_path_guarantee.
    + eapply store_next;[exact H|exact H0|]. constructor;eapply report_returns_memory;exact SCRIPT.
    + exact IHSCRIPT.
  - eapply call_procedure_guarantee;[exact H|eapply fault_procedure_guarantee;[exact H2|exact H1]|].
    intros value after [VALUE MEM];subst;exact IHSCRIPT.
  - subst cell. eapply call_procedure_guarantee;[exact H0|eapply write_detailed_guarantee;[exact H3|exact H4]|].
    intros value after [HISTORY [events [RUN POST]]].
    eapply procedure_guarantee_post;[exact (H6 events value after HISTORY (conj POST (proj2 (write_all_prefix_safety q input m events (live (Returnstate value Kstop after)) H3 RUN))) (or_introl eq_refl))|].
    intros final last [more RESULT];exists (emitted_trace events++more);exact RESULT.
Qed.
