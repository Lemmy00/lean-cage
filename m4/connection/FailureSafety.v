(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-callers.failure: All finite prefixes of the complete child-failure function. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Globalenvs Clight.
Require Import Slice IO Machine WriteMemory WriteAll StoreSteps Library LibraryMachine LibraryControl
  ProcessEffects Fault CallContexts CallProgressDraft HelperProgressDraft WriteCallers
  FreshMemoryDraft FailureSourceDraft FailureMemoryDraft FailureBranchesDraft FailureContractDraft.
Import ListNotations.
Open Scope Z_scope.

Theorem failure_write_live_progress : forall q input m local le k,
  write_owned q input m ->
  live_progress failure_ge (cell_of q)
    (write_call_initial q (failure_write_cont local le k) m).
Proof.
  intros q input m local le k OWN.
  eapply call_live_progress; [exact I|apply write_procedure_progress; exact OWN|].
  intros value after POST. eapply source_path_live_progress;
    [apply failure_after_write_path|apply exit_live_progress].
Qed.

Lemma failure_request_cell : forall cell fd local count,
  cell_of (failure_request cell fd local count) = cell.
Proof. destruct cell; reflexivity. Qed.

Lemma failure_short_live_progress : forall base built local cell fd stage error mode mode_bytes drop short k,
  failure_input cell base mode mode_bytes drop short -> old_memory base built ->
  ~ Mem.valid_block base local ->
  Mem.loadbytes built local 0 8 = Some (map Byte (failure_packet stage error)) ->
  live_progress failure_ge cell (failure_short_state local fd stage error short k built).
Proof.
  intros base built local cell fd stage error mode mode_bytes drop short k INPUT OLD FRESH PACKET.
  pose proof (failure_input_preserved _ _ _ _ _ _ _ INPUT OLD) as BUILT.
  change (live_progress failure_ge cell
    (plug_state (fault_initial (global_address short) Kstop built)
      (failure_short_cont local fd stage error k))).
  eapply call_live_progress; [exact I| |].
  - eapply fault_procedure_progress. exact (failure_short_input _ _ _ _ _ _ BUILT).
  - intros value after [VALUE AFTER]; subst value after. rewrite fault_value_matches.
    eapply source_path_live_progress; [apply failure_short_or_full_path with (cell:=cell)|].
    set (flag := matches_mode mode_bytes error_short_bytes).
    set (q := failure_request cell fd local (failure_count flag)).
    assert (OWN : write_owned q (firstn (Z.to_nat (failure_count flag)) (failure_packet stage error)) built).
    { unfold q. destruct flag.
      - exact (failure_packet_write_owned base built local cell fd stage error 3 (proj1 INPUT) FRESH OLD PACKET ltac:(lia)).
      - exact (failure_packet_write_owned base built local cell fd stage error 8 (proj1 INPUT) FRESH OLD PACKET ltac:(lia)). }
    change (live_progress failure_ge cell
      (write_call_initial q (failure_write_cont local (failure_write_temps fd stage error flag) k) built)).
    rewrite <- (failure_request_cell cell fd local (failure_count flag)).
    apply failure_write_live_progress with (input:=firstn (Z.to_nat (failure_count flag)) (failure_packet stage error)).
    exact OWN.
Qed.

Lemma failure_drop_live_progress : forall base built local cell fd stage error mode mode_bytes drop short k,
  failure_input cell base mode mode_bytes drop short -> old_memory base built ->
  ~ Mem.valid_block base local ->
  Mem.loadbytes built local 0 8 = Some (map Byte (failure_packet stage error)) ->
  live_progress failure_ge cell (failure_drop_state local fd stage error drop k built).
Proof.
  intros base built local cell fd stage error mode mode_bytes drop short k INPUT OLD FRESH PACKET.
  pose proof (failure_input_preserved _ _ _ _ _ _ _ INPUT OLD) as BUILT.
  change (live_progress failure_ge cell
    (plug_state (fault_initial (global_address drop) Kstop built)
      (failure_drop_cont local fd stage error k))).
  eapply call_live_progress; [exact I| |].
  - eapply fault_procedure_progress. exact (failure_drop_input _ _ _ _ _ _ BUILT).
  - intros value after [VALUE AFTER]; subst value after. rewrite fault_value_matches.
    destruct (matches_mode mode_bytes error_drop_bytes); cbn [Val.of_bool].
    + eapply source_path_live_progress; [apply failure_drop_path|apply exit_live_progress].
    + eapply source_path_live_progress; [apply failure_not_drop_path; exact (proj1 (proj2 (proj2 (proj2 (proj2 INPUT)))))|].
      exact (failure_short_live_progress base built local cell fd stage error mode mode_bytes drop short k INPUT OLD FRESH PACKET).
Qed.

Theorem failure_all_prefixes_defined : forall cell base fd stage error mode mode_bytes drop short k,
  failure_input cell base mode mode_bytes drop short -> is_call_cont k ->
  live_progress failure_ge cell (failure_initial fd stage error k base).
Proof.
  intros cell base fd stage error mode mode_bytes drop short k INPUT CALL.
  destruct (failure_prepare_execution base fd stage error drop k CALL
    (proj1 (proj2 (proj2 (proj2 INPUT))))) as [local [built [PATH [FRESH [OLD [RANGE PACKET]]]]]].
  eapply source_path_live_progress; [exact PATH|].
  exact (failure_drop_live_progress base built local cell fd stage error mode mode_bytes drop short k INPUT OLD FRESH PACKET).
Qed.

Theorem failure_never_returns : forall cell base fd stage error mode mode_bytes drop short events value after,
  failure_input cell base mode mode_bytes drop short ->
  ~ library_steps failure_ge cell (live (failure_initial fd stage error Kstop base)) events
    (live (Returnstate value Kstop after)).
Proof.
  intros cell base fd stage error mode mode_bytes drop short events value after INPUT.
  eapply live_progress_never_returns.
  exact (failure_all_prefixes_defined cell base fd stage error mode mode_bytes drop short Kstop INPUT I).
Qed.
