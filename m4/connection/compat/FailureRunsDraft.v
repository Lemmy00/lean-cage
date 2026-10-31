(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-callers.failure: Construct completed source executions without assuming publication. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Clight.
Require Import Slice IO Machine WriteMemory WriteAll StoreSteps Library LibraryMachine LibraryPreservation
  ProcessEffects Fault CallContexts CallEventsDraft ReportingTraceDraft WriteCallers
  FreshMemoryDraft FailureSourceDraft FailureMemoryDraft FailureBranchesDraft FailureContractDraft FailureSafetyDraft FailureTraceDraft.
Import ListNotations.
Open Scope Z_scope.

Lemma source_trace_empty : forall n,
  reporting_trace (map original_event (repeat (source_step E0) n)) = [].
Proof. induction n; cbn; auto. Qed.

Lemma selector_caller_success : forall cell m mode name xs ys k,
  fault_input failure_ge m mode name xs ys -> is_call_cont k ->
  exists events, library_steps failure_ge cell (live (fault_initial name k m)) events
    (live (Returnstate (fault_value xs ys) k m)) /\ reporting_trace events = [].
Proof.
  intros cell m mode name xs ys k INPUT CALL.
  destruct (fault_success_after_waits cell m mode name xs ys Kstop 0 INPUT) as [events [RUN FACTS]].
  exists events; split.
  - exact (plug_library_steps _ _ _ _ _ k CALL RUN).
  - apply reporting_trace_none. apply selector_reports_nothing.
    exact (fault_events_are_selectors _ _ _ _ _ _ _ actual_fault_symbols INPUT _ _ RUN).
Qed.

Lemma reports_nothing_trace : forall ge cell s events target,
  reports_nothing ge cell s -> library_steps ge cell (live s) events target -> reporting_trace events = [].
Proof. intros; apply reporting_trace_none; eapply H; eassumption. Qed.

Theorem failure_write_success_exit : forall q input m local le k,
  write_owned q input m ->
  exists events,
    library_steps failure_ge (cell_of q)
      (live (write_call_initial q (failure_write_cont local le k) m))
      (events ++ [exit_requested (Int.repr 125)]) (dead m) /\
    reporting_trace events = input.
Proof.
  intros q input m local le k OWN.
  destruct (write_caller_success q input m (failure_write_cont local le k) OWN I) as [events [WRITE BYTES]].
  exists (map original_event events ++ map original_event (repeat (source_step E0) 3)); split.
  - rewrite <- app_assoc. eapply library_steps_trans; [exact WRITE|].
    eapply library_steps_trans.
    + apply original_runs_preserved; eapply store_path_actual; apply failure_after_write_path.
    + econstructor; [apply exit_step|constructor].
  - rewrite reporting_trace_app, reporting_trace_original, source_trace_empty, app_nil_r; exact BYTES.
Qed.

Theorem failure_short_success_exit : forall base built local cell fd stage error mode mode_bytes drop short k,
  failure_input cell base mode mode_bytes drop short -> old_memory base built ->
  ~ Mem.valid_block base local ->
  Mem.loadbytes built local 0 8 = Some (map Byte (failure_packet stage error)) ->
  exists events,
    library_steps failure_ge cell (live (failure_short_state local fd stage error short k built))
      (events ++ [exit_requested (Int.repr 125)]) (dead built) /\
    reporting_trace events = firstn (Z.to_nat (failure_count (matches_mode mode_bytes error_short_bytes))) (failure_packet stage error).
Proof.
  intros base built local cell fd stage error mode mode_bytes drop short k INPUT OLD FRESH PACKET.
  pose proof (failure_input_preserved _ _ _ _ _ _ _ INPUT OLD) as BUILT.
  destruct (selector_caller_success cell built mode (global_address short) mode_bytes error_short_bytes
    (failure_short_cont local fd stage error k) (failure_short_input _ _ _ _ _ _ BUILT) I) as [selector [SELECT EMPTY]].
  rewrite fault_value_matches in SELECT.
  set (flag := matches_mode mode_bytes error_short_bytes).
  set (q := failure_request cell fd local (failure_count flag)).
  assert (OWN : write_owned q (firstn (Z.to_nat (failure_count flag)) (failure_packet stage error)) built).
  { unfold q. destruct flag.
    - exact (failure_packet_write_owned base built local cell fd stage error 3 (proj1 INPUT) FRESH OLD PACKET ltac:(lia)).
    - exact (failure_packet_write_owned base built local cell fd stage error 8 (proj1 INPUT) FRESH OLD PACKET ltac:(lia)). }
  destruct (failure_write_success_exit q _ built local (failure_write_temps fd stage error flag) k OWN) as [write [WRITE BYTES]].
  unfold q in WRITE; rewrite failure_request_cell in WRITE.
  exists (selector ++ map original_event (repeat (source_step E0) 6) ++ write); split.
  - repeat rewrite <- app_assoc. eapply library_steps_trans; [exact SELECT|].
    eapply library_steps_trans.
    + apply original_runs_preserved; eapply store_path_actual; apply failure_short_or_full_path with (cell:=cell).
    + exact WRITE.
  - rewrite !reporting_trace_app, EMPTY, source_trace_empty; cbn; exact BYTES.
Qed.

Theorem failure_drop_success_exit : forall base built local cell fd stage error mode mode_bytes drop short k,
  failure_input cell base mode mode_bytes drop short -> old_memory base built ->
  ~ Mem.valid_block base local ->
  Mem.loadbytes built local 0 8 = Some (map Byte (failure_packet stage error)) ->
  exists events,
    library_steps failure_ge cell (live (failure_drop_state local fd stage error drop k built))
      (events ++ [exit_requested (Int.repr 125)]) (dead built) /\
    reporting_trace events = selected_report mode_bytes stage error.
Proof.
  intros base built local cell fd stage error mode mode_bytes drop short k INPUT OLD FRESH PACKET.
  pose proof (failure_input_preserved _ _ _ _ _ _ _ INPUT OLD) as BUILT.
  destruct (selector_caller_success cell built mode (global_address drop) mode_bytes error_drop_bytes
    (failure_drop_cont local fd stage error k) (failure_drop_input _ _ _ _ _ _ BUILT) I) as [selector [SELECT EMPTY]].
  rewrite fault_value_matches in SELECT. unfold selected_report.
  destruct (matches_mode mode_bytes error_drop_bytes); cbn [Val.of_bool] in SELECT.
  - exists (selector ++ map original_event (repeat (source_step E0) 5)); split.
    + rewrite <- app_assoc. eapply library_steps_trans; [exact SELECT|].
      eapply library_steps_trans.
      * apply original_runs_preserved; eapply store_path_actual; apply failure_drop_path.
      * econstructor; [apply exit_step|constructor].
    + rewrite reporting_trace_app, EMPTY, source_trace_empty; reflexivity.
  - destruct (failure_short_success_exit base built local cell fd stage error mode mode_bytes drop short k INPUT OLD FRESH PACKET)
      as [report [REPORT BYTES]].
    exists (selector ++ map original_event (repeat (source_step E0) 6) ++ report); split.
    + repeat rewrite <- app_assoc. eapply library_steps_trans; [exact SELECT|].
      eapply library_steps_trans.
      * apply original_runs_preserved; eapply store_path_actual; apply failure_not_drop_path.
        exact (proj1 (proj2 (proj2 (proj2 (proj2 INPUT))))).
      * exact REPORT.
    + rewrite !reporting_trace_app, EMPTY, source_trace_empty; cbn; exact BYTES.
Qed.

Theorem failure_successful_exit_exists : forall cell base fd stage error mode mode_bytes drop short k,
  failure_input cell base mode mode_bytes drop short -> is_call_cont k ->
  exists events final,
    library_steps failure_ge cell (live (failure_initial fd stage error k base))
      (events ++ [exit_requested (Int.repr 125)]) (dead final) /\
    reporting_trace events = selected_report mode_bytes stage error.
Proof.
  intros cell base fd stage error mode mode_bytes drop short k INPUT CALL.
  destruct (failure_prepare_execution base fd stage error drop k CALL
    (proj1 (proj2 (proj2 (proj2 INPUT))))) as [local [built [PATH [FRESH [OLD [RANGE PACKET]]]]]].
  destruct (failure_drop_success_exit base built local cell fd stage error mode mode_bytes drop short k INPUT OLD FRESH PACKET)
    as [report [REPORT BYTES]].
  exists (map original_event (repeat (source_step E0) 96) ++ report), built; split.
  - rewrite <- app_assoc. eapply library_steps_trans.
    + apply original_runs_preserved; eapply store_path_actual; exact PATH.
    + exact REPORT.
  - rewrite reporting_trace_app, source_trace_empty; cbn; exact BYTES.
Qed.
