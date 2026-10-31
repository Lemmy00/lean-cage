(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-callers.control: Exact reporting prefixes, including interrupted transfers. *)
From Coq Require Import List.
From compcert Require Import Integers AST Values Memory Events Clight.
Require Import Slice IO Machine WriteMemory WriteAll StoreSteps Library LibraryMachine LibraryPreservation
  LibraryControl Fault CallContexts CallPaths WriteCallers CallEventsDraft ExitControlDraft.
Import ListNotations.

Definition reporting_bytes ev := match ev with original_event old => emitted old | _ => [] end.
Definition reporting_trace events := flat_map reporting_bytes events.
Definition reports_prefix ge cell start bytes := forall events target,
  library_steps ge cell (live start) events target -> exists rest, bytes = reporting_trace events ++ rest.
Definition reports_nothing ge cell start := event_contract ge cell start (fun ev => reporting_bytes ev = []).

Lemma reporting_trace_original : forall events, reporting_trace (map original_event events) = emitted_trace events.
Proof. induction events; cbn; [reflexivity|]. change (emitted a ++ reporting_trace (map original_event events) = emitted a ++ emitted_trace events). rewrite IHevents; reflexivity. Qed.
Lemma reporting_trace_app : forall first rest, reporting_trace (first ++ rest) = reporting_trace first ++ reporting_trace rest.
Proof. intros; apply flat_map_app. Qed.
Lemma reporting_trace_none : forall events, Forall (fun ev => reporting_bytes ev = []) events -> reporting_trace events = [].
Proof. intros events H; induction H; [reflexivity|].
  change (reporting_bytes x ++ reporting_trace l = []). rewrite H, IHForall; reflexivity. Qed.
Lemma selector_reports_nothing : forall events, Forall selector_event events -> Forall (fun ev => reporting_bytes ev=[]) events.
Proof. intros events H; eapply Forall_impl; [|exact H]. intros ev GOOD; destruct ev; cbn in *; try reflexivity. destruct ev; cbn in *; tauto. Qed.

Theorem source_path_reports_prefix : forall ge cell P start count last bytes,
  store_path ge P start count last -> reports_prefix ge cell last bytes -> reports_prefix ge cell start bytes.
Proof.
  intros ge cell P start count last bytes PATH LAST; induction PATH; [exact LAST|].
  intros events target RUN; inversion RUN; subst; [exists bytes; reflexivity|].
  pose proof H0 as [IN _].
  match goal with STEP : library_step _ _ _ _ _ |- _ =>
    destruct (internal_boundary_unchanged _ _ _ _ _ IN STEP) as [old [EV OLD]] end; subst.
  destruct (store_edge_cases _ _ _ _ _ _ H0 OLD) as [[EV TARGET]|[EV TARGET]]; subst.
  - cbn [reporting_trace reporting_bytes emitted flat_map app]. eapply (IHPATH LAST _ _); eassumption.
  - match goal with TAIL : library_steps _ _ (dead _) _ _ |- _ =>
      destruct (library_dead_steps _ _ _ _ _ TAIL) as [ES EQ] end; subst.
    exists bytes; reflexivity.
Qed.

Theorem selector_call_reports_prefix : forall cell m mode name xs ys suffix bytes,
  fault_input (Clight.globalenv Slice.prog) m mode name xs ys -> is_call_cont suffix ->
  reports_prefix (Clight.globalenv Slice.prog) cell
    (Returnstate (fault_value xs ys) suffix m) bytes ->
  reports_prefix (Clight.globalenv Slice.prog) cell
    (plug_state (fault_initial name Kstop m) suffix) bytes.
Proof.
  intros cell m mode name xs ys suffix bytes OWN CALL RETURN events target RUN.
  destruct (caller_run_decomposition _ _ _ _ _ _ CALL RUN)
    as [[last [PREFIX SAME]]|[before [after [value [final [ES [PREFIX TAIL]]]]]]].
  - pose proof (fault_events_are_selectors _ _ _ _ _ _ _ actual_fault_symbols OWN _ _ PREFIX) as EVENTS.
    pose proof (reporting_trace_none _ (selector_reports_nothing _ EVENTS)) as EMPTY.
    exists bytes; rewrite EMPTY; reflexivity.
  - pose proof (fault_events_are_selectors _ _ _ _ _ _ _ actual_fault_symbols OWN _ _ PREFIX) as EVENTS.
    pose proof (reporting_trace_none _ (selector_reports_nothing _ EVENTS)) as EMPTY.
    destruct (fault_return_exact _ _ _ _ _ _ _ _ _ OWN PREFIX) as [VALUE MEM]; subst value final events.
    rewrite reporting_trace_app, EMPTY; cbn. exact (RETURN _ _ TAIL).
Qed.

Theorem write_call_reports_prefix : forall q input m suffix,
  write_owned q input m -> is_call_cont suffix ->
  (forall value after, reports_nothing (Clight.globalenv Slice.prog) (cell_of q)
    (Returnstate value suffix after)) ->
  reports_prefix (Clight.globalenv Slice.prog) (cell_of q) (write_call_initial q suffix m) input.
Proof.
  intros q input m suffix OWN CALL RETURN events target RUN.
  destruct (write_caller_decomposition _ _ _ _ _ _ OWN CALL RUN)
    as [[original [last [ES [EQ [LOCAL [PRESERVED PREFIX]]]]]]|
      [before [after [value [final [ES [POST [LOCAL TAIL]]]]]]]].
  - subst events; rewrite reporting_trace_original; exact PREFIX.
  - pose proof (reporting_trace_none _ (RETURN value final _ _ TAIL)) as EMPTY.
    subst events; rewrite reporting_trace_app, reporting_trace_original, EMPTY, app_nil_r.
    exact (proj2 (write_all_prefix_safety _ _ _ _ _ OWN LOCAL)).
Qed.

Theorem exit_reports_nothing : forall ge cell code k m,
  reports_nothing ge cell (Callstate exit_definition [Vint code] k m).
Proof.
  intros ge cell code k m events target RUN.
  destruct (exit_histories _ _ _ _ _ _ _ RUN) as [[n [ES EQ]]|[[n [ES EQ]]|[n [ES EQ]]]]; subst events.
  - apply Forall_forall; intros ev IN; apply repeat_spec in IN; subst ev; reflexivity.
  - apply Forall_app; split; [apply Forall_forall; intros ev IN; apply repeat_spec in IN; subst ev; reflexivity|repeat constructor].
  - apply Forall_app; split; [apply Forall_forall; intros ev IN; apply repeat_spec in IN; subst ev; reflexivity|repeat constructor].
Qed.
