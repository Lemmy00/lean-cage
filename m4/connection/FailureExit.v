(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-callers.failure: Every observed exit attempt in the complete function has code 125. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Clight.
Require Import Slice IO Machine WriteMemory WriteAll StoreSteps Library LibraryMachine ProcessEffects Fault
  CallContexts CallEventsDraft ExitEventsDraft WriteCallers FreshMemoryDraft FailureSourceDraft
  FailureMemoryDraft FailureBranchesDraft FailureContractDraft FailureSafetyDraft.
Import ListNotations.
Open Scope Z_scope.

Lemma failure_after_write_exit_code : forall cell local le k value m,
  event_contract failure_ge cell (Returnstate value (failure_write_cont local le k) m)
    (exit_code_event (Int.repr 125)).
Proof.
  intros; eapply source_path_event_contract; [apply failure_after_write_path|exact I|exact I|apply exit_event_contract].
Qed.

Lemma failure_short_exit_code : forall base built local cell fd stage error mode mode_bytes drop short k,
  failure_input cell base mode mode_bytes drop short -> old_memory base built ->
  ~ Mem.valid_block base local ->
  Mem.loadbytes built local 0 8 = Some (map Byte (failure_packet stage error)) ->
  event_contract failure_ge cell (failure_short_state local fd stage error short k built) (exit_code_event (Int.repr 125)).
Proof.
  intros base built local cell fd stage error mode mode_bytes drop short k INPUT OLD FRESH PACKET.
  pose proof (failure_input_preserved _ _ _ _ _ _ _ INPUT OLD) as BUILT.
  pose proof (failure_short_input _ _ _ _ _ _ BUILT) as OWNFAULT.
  change (event_contract failure_ge cell
    (plug_state (fault_initial (global_address short) Kstop built)
      (failure_short_cont local fd stage error k)) (exit_code_event (Int.repr 125))).
  apply call_event_contract; [exact I|eapply fault_event_contract; exact OWNFAULT|].
  intros events value after RUN.
  destruct (fault_return_exact _ _ _ _ _ _ _ _ _ OWNFAULT RUN) as [V M]; subst value after.
  rewrite fault_value_matches. eapply source_path_event_contract;
    [apply failure_short_or_full_path with (cell:=cell)|exact I|exact I|].
  set (flag := matches_mode mode_bytes error_short_bytes).
  set (q := failure_request cell fd local (failure_count flag)).
  assert (OWN : write_owned q (firstn (Z.to_nat (failure_count flag)) (failure_packet stage error)) built).
  { unfold q. destruct flag.
    - exact (failure_packet_write_owned base built local cell fd stage error 3 (proj1 INPUT) FRESH OLD PACKET ltac:(lia)).
    - exact (failure_packet_write_owned base built local cell fd stage error 8 (proj1 INPUT) FRESH OLD PACKET ltac:(lia)). }
  change (event_contract failure_ge cell
    (write_call_initial q (failure_write_cont local (failure_write_temps fd stage error flag) k) built) (exit_code_event (Int.repr 125))).
  rewrite <- (failure_request_cell cell fd local (failure_count flag)).
  apply call_event_contract; [exact I|eapply write_event_contract; exact OWN|].
  intros; apply failure_after_write_exit_code.
Qed.

Lemma failure_drop_exit_code : forall base built local cell fd stage error mode mode_bytes drop short k,
  failure_input cell base mode mode_bytes drop short -> old_memory base built ->
  ~ Mem.valid_block base local ->
  Mem.loadbytes built local 0 8 = Some (map Byte (failure_packet stage error)) ->
  event_contract failure_ge cell (failure_drop_state local fd stage error drop k built) (exit_code_event (Int.repr 125)).
Proof.
  intros base built local cell fd stage error mode mode_bytes drop short k INPUT OLD FRESH PACKET.
  pose proof (failure_input_preserved _ _ _ _ _ _ _ INPUT OLD) as BUILT.
  pose proof (failure_drop_input _ _ _ _ _ _ BUILT) as OWNFAULT.
  change (event_contract failure_ge cell
    (plug_state (fault_initial (global_address drop) Kstop built)
      (failure_drop_cont local fd stage error k)) (exit_code_event (Int.repr 125))).
  apply call_event_contract; [exact I|eapply fault_event_contract; exact OWNFAULT|].
  intros events value after RUN.
  destruct (fault_return_exact _ _ _ _ _ _ _ _ _ OWNFAULT RUN) as [V M]; subst value after.
  rewrite fault_value_matches. destruct (matches_mode mode_bytes error_drop_bytes); cbn [Val.of_bool].
  - eapply source_path_event_contract; [apply failure_drop_path|exact I|exact I|apply exit_event_contract].
  - eapply source_path_event_contract;
      [apply failure_not_drop_path; exact (proj1 (proj2 (proj2 (proj2 (proj2 INPUT)))))|exact I|exact I|].
    exact (failure_short_exit_code base built local cell fd stage error mode mode_bytes drop short k INPUT OLD FRESH PACKET).
Qed.

Theorem failure_only_exit_125 : forall cell base fd stage error mode mode_bytes drop short k events target code,
  failure_input cell base mode mode_bytes drop short -> is_call_cont k ->
  library_steps failure_ge cell (live (failure_initial fd stage error k base)) events target ->
  In (exit_requested code) events -> code=Int.repr 125.
Proof.
  intros cell base fd stage error mode mode_bytes drop short k events target code INPUT CALL RUN IN.
  destruct (failure_prepare_execution base fd stage error drop k CALL
    (proj1 (proj2 (proj2 (proj2 INPUT))))) as [local [built [PATH [FRESH [OLD [RANGE PACKET]]]]]].
  pose proof (source_path_event_contract _ cell _ _ _ _ (exit_code_event (Int.repr 125)) PATH I I
    (failure_drop_exit_code base built local cell fd stage error mode mode_bytes drop short k INPUT OLD FRESH PACKET)
    events target RUN) as EVENTS.
  rewrite Forall_forall in EVENTS. exact (EVENTS _ IN).
Qed.
