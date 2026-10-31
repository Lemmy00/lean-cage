(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-callers.failure: A complete failed-report execution still requests exit. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Clight.
Require Import Slice IO Machine WriteMemory WriteAll WriteWitnesses StoreSteps Library LibraryMachine LibraryPreservation
  ProcessEffects Fault CallContexts ReportingTraceDraft WriteCallers FreshMemoryDraft FailureSourceDraft
  FailureMemoryDraft FailureBranchesDraft FailureContractDraft FailureSafetyDraft FailureTraceDraft FailureRunsDraft.
Import ListNotations.
Open Scope Z_scope.

Theorem failure_reaches_write_call : forall cell base fd stage error mode mode_bytes drop short k,
  failure_input cell base mode mode_bytes drop short -> is_call_cont k ->
  matches_mode mode_bytes error_drop_bytes = false ->
  exists local built prefix,
    library_steps failure_ge cell (live (failure_initial fd stage error k base)) prefix
      (live (write_call_initial
        (failure_request cell fd local (failure_count (matches_mode mode_bytes error_short_bytes)))
        (failure_write_cont local (failure_write_temps fd stage error (matches_mode mode_bytes error_short_bytes)) k) built)) /\
    write_owned (failure_request cell fd local (failure_count (matches_mode mode_bytes error_short_bytes)))
      (selected_report mode_bytes stage error) built /\
    reporting_trace prefix = [].
Proof.
  intros cell base fd stage error mode mode_bytes drop short k INPUT CALL NOTDROP.
  destruct (failure_prepare_execution base fd stage error drop k CALL
    (proj1 (proj2 (proj2 (proj2 INPUT))))) as [local [built [PATH [FRESH [OLD [RANGE PACKET]]]]]].
  pose proof (failure_input_preserved _ _ _ _ _ _ _ INPUT OLD) as BUILT.
  destruct (selector_caller_success cell built mode (global_address drop) mode_bytes error_drop_bytes
    (failure_drop_cont local fd stage error k) (failure_drop_input _ _ _ _ _ _ BUILT) I) as [drop_events [DROP EMPTYD]].
  rewrite fault_value_matches, NOTDROP in DROP.
  destruct (selector_caller_success cell built mode (global_address short) mode_bytes error_short_bytes
    (failure_short_cont local fd stage error k) (failure_short_input _ _ _ _ _ _ BUILT) I) as [short_events [SHORT EMPTYS]].
  rewrite fault_value_matches in SHORT.
  exists local, built, (map original_event (repeat (source_step E0) 96) ++ drop_events ++
    map original_event (repeat (source_step E0) 6) ++ short_events ++
    map original_event (repeat (source_step E0) 6)).
  split.
  - eapply library_steps_trans; [apply original_runs_preserved; eapply store_path_actual; exact PATH|].
    eapply library_steps_trans; [exact DROP|].
    eapply library_steps_trans.
    + apply original_runs_preserved; eapply store_path_actual; apply failure_not_drop_path.
      exact (proj1 (proj2 (proj2 (proj2 (proj2 INPUT))))).
    + eapply library_steps_trans; [exact SHORT|].
      apply original_runs_preserved; eapply store_path_actual; apply failure_short_or_full_path with (cell:=cell).
  - split.
    + unfold selected_report; rewrite NOTDROP.
      destruct (matches_mode mode_bytes error_short_bytes).
      * exact (failure_packet_write_owned base built local cell fd stage error 3 (proj1 INPUT) FRESH OLD PACKET ltac:(lia)).
      * exact (failure_packet_write_owned base built local cell fd stage error 8 (proj1 INPUT) FRESH OLD PACKET ltac:(lia)).
    + rewrite !reporting_trace_app, !source_trace_empty, EMPTYD, EMPTYS; reflexivity.
Qed.

Lemma failure_reply_in : forall events error,
  In (failure error) (replies events) -> exists q, In (io_step q (failure error)) events.
Proof.
  intros events error IN. unfold replies in IN; apply in_flat_map in IN.
  destruct IN as [ev [EVENT VALUE]]. destruct ev; cbn in VALUE; try contradiction.
  destruct VALUE as [EQ|EQ]; [subst|contradiction]; eauto.
Qed.

Theorem failure_failed_report_exit_exists : forall cell base fd stage error mode mode_bytes drop short k write_error,
  failure_input cell base mode mode_bytes drop short -> is_call_cont k ->
  matches_mode mode_bytes error_drop_bytes = false -> write_error <> Int.repr 4 ->
  exists events final request,
    library_steps failure_ge cell (live (failure_initial fd stage error k base))
      (events ++ [exit_requested (Int.repr 125)]) (dead final) /\
    In (original_event (io_step request (failure write_error))) events.
Proof.
  intros cell base fd stage error mode mode_bytes drop short k write_error INPUT CALL NOTDROP ERROR.
  destruct (failure_reaches_write_call cell base fd stage error mode mode_bytes drop short k INPUT CALL NOTDROP)
    as [local [built [prefix [BEFORE [OWN EMPTY]]]]].
  assert (NONEMPTY : selected_report mode_bytes stage error <> []).
  { unfold selected_report; rewrite NOTDROP; destruct (matches_mode mode_bytes error_short_bytes); discriminate. }
  set (q := failure_request cell fd local (failure_count (matches_mode mode_bytes error_short_bytes))).
  set (le := failure_write_temps fd stage error (matches_mode mode_bytes error_short_bytes)).
  destruct (write_caller_error q _ built (failure_write_cont local le k) write_error OWN NONEMPTY I ERROR)
    as [write [after [WRITE REPLIES]]].
  unfold q in WRITE; rewrite failure_request_cell in WRITE.
  destruct (failure_reply_in write write_error) as [request ERRORIN]; [rewrite REPLIES; left; reflexivity|].
  exists (prefix ++ map original_event write ++ map original_event (repeat (source_step E0) 3)), after, request.
  split.
  - repeat rewrite <- app_assoc. eapply library_steps_trans; [exact BEFORE|].
    eapply library_steps_trans; [exact WRITE|]. eapply library_steps_trans.
    + apply original_runs_preserved; eapply store_path_actual; apply failure_after_write_path.
    + econstructor; [apply exit_step|constructor].
  - apply in_or_app; right; apply in_or_app; left; apply in_map; exact ERRORIN.
Qed.

Theorem failure_partial_loss_exists : forall waits cell base fd stage error mode mode_bytes drop short k first rest,
  failure_input cell base mode mode_bytes drop short -> is_call_cont k ->
  matches_mode mode_bytes error_drop_bytes = false ->
  selected_report mode_bytes stage error = first ++ rest -> first <> [] ->
  exists events final,
    library_steps failure_ge cell (live (failure_initial fd stage error k base)) events (dead final) /\
    reporting_trace events = first /\
    exists before request, events = before ++
      map original_event (repeat wait_step waits ++ [partial_loss request first None]).
Proof.
  intros waits cell base fd stage error mode mode_bytes drop short k first rest INPUT CALL NOTDROP SPLIT NONEMPTY.
  destruct (failure_reaches_write_call cell base fd stage error mode mode_bytes drop short k INPUT CALL NOTDROP)
    as [local [built [prefix [BEFORE [OWN EMPTY]]]]].
  rewrite SPLIT in OWN.
  set (q := failure_request cell fd local (failure_count (matches_mode mode_bytes error_short_bytes))).
  set (le := failure_write_temps fd stage error (matches_mode mode_bytes error_short_bytes)).
  destruct (write_caller_partial_loss waits q first rest built (failure_write_cont local le k) OWN NONEMPTY I)
    as [write [WRITE [BYTES [REPLIES [n ES]]]]].
  unfold q in WRITE; rewrite failure_request_cell in WRITE.
  exists (prefix ++ map original_event write), built; split.
  - eapply library_steps_trans; [exact BEFORE|exact WRITE].
  - split; [rewrite reporting_trace_app, EMPTY, reporting_trace_original; exact BYTES|].
    exists (prefix ++ map original_event (repeat (source_step E0) n)), (suffix q 0).
    rewrite ES, map_app, app_assoc; reflexivity.
Qed.
