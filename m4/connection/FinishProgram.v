(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.finish: Compose full sender execution with the real publication-independent exit mapping. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers Values Memory Clight.
Require Import Slice IO Machine Deterministic ClightSteps WriteAll StoreSteps Library LibraryMachine CallContexts
  CallPaths CallProgress SourceGuarantees FreshMemory ResultLayout FrameRecord FrameCopy
  SenderSource SenderSelectors SenderReportMemory SenderProgram
  FinishMemory FinishSource FinishPreparation FinishControl ProcedureCalls.
Import ListNotations.
Open Scope Z_scope.
Theorem finish_whole_source_guarantee : forall cell base input ofs r digest mode mode_bytes locations,
  sender_input cell base input ofs r digest mode mode_bytes locations ->
  procedure_guarantee result_ge cell (sender_preserved cell base) (finish_result base r)
    (finish_initial input ofs Kstop base).
Proof.
  intros cell base input ofs r digest mode mode_bytes locations INPUT.
  pose proof INPUT as [OWN [SELECTORS [magic [SYM MAGIC]]]].
  destruct (finish_preparation_exists base input ofs r digest Kstop OWN)
    as [allocated [local [copied [ALLOC [PATH [OLD [COPIED FREE]]]]]]].
  assert (FRESH : ~Mem.valid_block base local) by (eapply Mem.fresh_block_alloc;exact ALLOC).
  assert (NE : local<>tls_block cell) by (eapply fresh_tls_separate;[exact (proj1 SELECTORS)|exact FRESH]).
  assert (PRESERVED : sender_preserved cell base copied) by (apply old_sender_preserved;exact OLD).
  assert (CHILDINPUT : sender_input cell copied local 0 r digest mode mode_bytes locations).
  { split;[exact COPIED|]. split;[eapply sender_selectors_old;[exact OLD|exact SELECTORS]|].
    exists magic;split;[exact SYM|eapply old_memory_readable;[exact OLD|exact MAGIC]]. }
  eapply source_path_guarantee;[eapply store_path_consequence;[exact PATH|intros;apply old_sender_preserved;assumption]|].
  eapply source_path_guarantee.
  - eapply store_next;[exact PRESERVED|apply unchanged_store_edge;WriteAll.structural|].
    eapply store_next;[exact PRESERVED|apply finish_send_source|]. constructor;exact PRESERVED.
  - change (procedure_guarantee result_ge cell (sender_preserved cell base) (finish_result base r)
      (plug_state (sender_initial Int.one Int64.zero local 0 Kstop copied)
        (finish_sender_cont local (finish_temps input ofs) Kstop))).
    eapply call_procedure_guarantee;[exact I| |].
    + eapply procedure_guarantee_consequence.
      * apply procedure_preservation_post;exact (sender_whole_source_guarantee cell copied Int.one Int64.zero
          local 0 r digest mode mode_bytes locations CHILDINPUT).
      * intros after GOOD;eapply sender_preserved_trans;[exact PRESERVED|exact GOOD].
      * intros value after [GOOD RESULT];exact GOOD.
    + intros value after GOOD.
      assert (AFTER : sender_preserved cell base after) by (eapply sender_preserved_trans;[exact PRESERVED|exact GOOD]).
      eapply source_path_guarantee.
      * eapply store_next;[exact AFTER|apply unchanged_store_edge;WriteAll.structural|].
        eapply store_next;[exact AFTER|apply unchanged_store_edge;WriteAll.structural|].
        constructor;exact AFTER.
      * apply source_returns_guarantee;eapply finish_after_send_source;[exact FRESH|exact AFTER|
          eapply preserved_frame_owned;[exact GOOD|exact NE|exact COPIED]|
          eapply preserved_frame_freeable;[exact GOOD|exact NE|exact FREE]|reflexivity].
Qed.
Theorem finish_all_returns : forall cell base input ofs r digest mode mode_bytes locations events value after,
  sender_input cell base input ofs r digest mode mode_bytes locations ->
  library_steps result_ge cell (live (finish_initial input ofs Kstop base)) events
    (live (Returnstate value Kstop after)) -> finish_result base r value after.
Proof.
  intros;eapply procedure_return_post;[exact (proj2 (finish_whole_source_guarantee _ _ _ _ _ _ _ _ _ H))|exact H0].
Qed.
Theorem finish_all_prefixes : forall cell base input ofs r digest mode mode_bytes locations events target,
  sender_input cell base input ofs r digest mode mode_bytes locations ->
  library_steps result_ge cell (live (finish_initial input ofs Kstop base)) events target ->
  sender_preserved cell base (routine_memory target).
Proof. intros;exact (proj1 (finish_whole_source_guarantee _ _ _ _ _ _ _ _ _ H) _ _ H0). Qed.
Theorem finish_defined_prefix : forall cell base input ofs r digest mode mode_bytes locations events s,
  sender_input cell base input ofs r digest mode mode_bytes locations ->
  library_steps result_ge cell (live (finish_initial input ofs Kstop base)) events (live s) ->
  (exists value after,s=Returnstate value Kstop after /\ finish_result base r value after) \/
  (exists ev target,LibraryControl.control_progress ev /\ library_step result_ge cell (live s) ev target).
Proof. intros;exact (proj2 (finish_whole_source_guarantee _ _ _ _ _ _ _ _ _ H) _ _ H0). Qed.
