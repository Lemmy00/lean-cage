(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-callers.failure: Every complete-source trace emits a prefix of the selected packet. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Events Clight.
Require Import Slice IO Machine WriteMemory WriteAll StoreSteps Library LibraryMachine
  ProcessEffects Fault CallContexts CallEventsDraft ReportingTraceDraft WriteCallers
  FreshMemoryDraft FailureSourceDraft FailureMemoryDraft FailureBranchesDraft FailureContractDraft FailureSafetyDraft.
Import ListNotations.
Open Scope Z_scope.

Definition selected_report mode_bytes stage error :=
  if matches_mode mode_bytes error_drop_bytes then [] else
  firstn (Z.to_nat (failure_count (matches_mode mode_bytes error_short_bytes))) (failure_packet stage error).

Lemma failure_after_write_reports_nothing : forall cell local le k value m,
  reports_nothing failure_ge cell (Returnstate value (failure_write_cont local le k) m).
Proof.
  intros. eapply source_path_event_contract; [apply failure_after_write_path|reflexivity|reflexivity|].
  apply exit_reports_nothing.
Qed.

Lemma failure_short_reports_prefix : forall base built local cell fd stage error mode mode_bytes drop short k,
  failure_input cell base mode mode_bytes drop short -> old_memory base built ->
  ~ Mem.valid_block base local ->
  Mem.loadbytes built local 0 8 = Some (map Byte (failure_packet stage error)) ->
  reports_prefix failure_ge cell (failure_short_state local fd stage error short k built)
    (firstn (Z.to_nat (failure_count (matches_mode mode_bytes error_short_bytes))) (failure_packet stage error)).
Proof.
  intros base built local cell fd stage error mode mode_bytes drop short k INPUT OLD FRESH PACKET.
  pose proof (failure_input_preserved _ _ _ _ _ _ _ INPUT OLD) as BUILT.
  change (reports_prefix failure_ge cell
    (plug_state (fault_initial (global_address short) Kstop built)
      (failure_short_cont local fd stage error k))
    (firstn (Z.to_nat (failure_count (matches_mode mode_bytes error_short_bytes))) (failure_packet stage error))).
  eapply selector_call_reports_prefix; [exact (failure_short_input _ _ _ _ _ _ BUILT)|exact I|].
  rewrite fault_value_matches. eapply source_path_reports_prefix;
    [apply failure_short_or_full_path with (cell:=cell)|].
  set (flag := matches_mode mode_bytes error_short_bytes).
  set (q := failure_request cell fd local (failure_count flag)).
  assert (OWN : write_owned q (firstn (Z.to_nat (failure_count flag)) (failure_packet stage error)) built).
  { unfold q. destruct flag.
    - exact (failure_packet_write_owned base built local cell fd stage error 3 (proj1 INPUT) FRESH OLD PACKET ltac:(lia)).
    - exact (failure_packet_write_owned base built local cell fd stage error 8 (proj1 INPUT) FRESH OLD PACKET ltac:(lia)). }
  change (reports_prefix failure_ge cell
    (write_call_initial q (failure_write_cont local (failure_write_temps fd stage error flag) k) built)
    (firstn (Z.to_nat (failure_count flag)) (failure_packet stage error))).
  rewrite <- (failure_request_cell cell fd local (failure_count flag)).
  apply write_call_reports_prefix; [exact OWN|exact I|].
  intros; apply failure_after_write_reports_nothing.
Qed.

Lemma failure_drop_reports_prefix : forall base built local cell fd stage error mode mode_bytes drop short k,
  failure_input cell base mode mode_bytes drop short -> old_memory base built ->
  ~ Mem.valid_block base local ->
  Mem.loadbytes built local 0 8 = Some (map Byte (failure_packet stage error)) ->
  reports_prefix failure_ge cell (failure_drop_state local fd stage error drop k built)
    (selected_report mode_bytes stage error).
Proof.
  intros base built local cell fd stage error mode mode_bytes drop short k INPUT OLD FRESH PACKET.
  pose proof (failure_input_preserved _ _ _ _ _ _ _ INPUT OLD) as BUILT.
  change (reports_prefix failure_ge cell
    (plug_state (fault_initial (global_address drop) Kstop built)
      (failure_drop_cont local fd stage error k)) (selected_report mode_bytes stage error)).
  eapply selector_call_reports_prefix; [exact (failure_drop_input _ _ _ _ _ _ BUILT)|exact I|].
  rewrite fault_value_matches. unfold selected_report.
  destruct (matches_mode mode_bytes error_drop_bytes); cbn [Val.of_bool].
  - eapply source_path_reports_prefix; [apply failure_drop_path|].
    intros events target RUN. pose proof (reporting_trace_none _ (exit_reports_nothing _ _ _ _ _ _ _ RUN)) as EMPTY.
    exists []; rewrite EMPTY; reflexivity.
  - eapply source_path_reports_prefix; [apply failure_not_drop_path; exact (proj1 (proj2 (proj2 (proj2 (proj2 INPUT)))))|].
    exact (failure_short_reports_prefix base built local cell fd stage error mode mode_bytes drop short k INPUT OLD FRESH PACKET).
Qed.

Theorem failure_reporting_prefix : forall cell base fd stage error mode mode_bytes drop short k events target,
  failure_input cell base mode mode_bytes drop short -> is_call_cont k ->
  library_steps failure_ge cell (live (failure_initial fd stage error k base)) events target ->
  exists rest, selected_report mode_bytes stage error = reporting_trace events ++ rest.
Proof.
  intros cell base fd stage error mode mode_bytes drop short k events target INPUT CALL RUN.
  destruct (failure_prepare_execution base fd stage error drop k CALL
    (proj1 (proj2 (proj2 (proj2 INPUT))))) as [local [built [PATH [FRESH [OLD [RANGE PACKET]]]]]].
  exact (source_path_reports_prefix _ _ _ _ _ _ _ PATH
    (failure_drop_reports_prefix base built local cell fd stage error mode mode_bytes drop short k INPUT OLD FRESH PACKET)
    events target RUN).
Qed.
