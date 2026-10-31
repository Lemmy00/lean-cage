(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.evidence: Whole-source finish returns from arbitrary allocated caller records. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers Values Memory Events Clight.
Require Import Slice IO Machine ClightSteps WriteAll StoreSteps Library LibraryMachine LibraryPreservation Fault
  CallContexts CallPaths SourcePaths SourceGuarantees FreshMemory ResultLayout FrameRecord FrameCopy
  SenderSource SenderSelectors SenderReportMemory SenderProgram SenderRuns
  FinishMemory FinishSource FinishPreparation FinishControl FinishProgram.
Import ListNotations.
Open Scope Z_scope.
Theorem finish_finite_return_exists : forall cell base input ofs r digest mode mode_bytes locations,
  sender_input cell base input ofs r digest mode mode_bytes locations ->
  exists events after,
    library_steps result_ge cell (live (finish_initial input ofs Kstop base)) events
      (live (Returnstate (Vint (finish_exit_word r)) Kstop after)) /\
    finish_result base r (Vint (finish_exit_word r)) after.
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
  destruct (sender_finite_return_exists cell copied Int.one Int64.zero local 0 r digest mode mode_bytes locations CHILDINPUT)
    as [send [value [sent [SEND RESULT]]]].
  pose proof (proj1 (sender_all_prefixes _ _ _ _ _ _ _ _ _ _ _ _ _ CHILDINPUT SEND)) as GOOD.
  change (sender_preserved cell copied sent) in GOOD.
  assert (AFTER : sender_preserved cell base sent) by (eapply sender_preserved_trans;[exact PRESERVED|exact GOOD]).
  destruct (source_returns_run result_ge cell _ _ _ (finish_after_send_source cell base sent local
    (finish_temps input ofs) Kstop r digest FRESH AFTER
    (preserved_frame_owned _ _ _ _ _ _ _ GOOD NE COPIED)
    (preserved_frame_freeable _ _ _ _ GOOD NE FREE) eq_refl)) as [last [exitcode [final [TAIL [PROGRESS [VALUE POST]]]]]].
  subst exitcode.
  exists (map original_event (repeat (source_step E0) 6)++send++
    map original_event (repeat (source_step E0) 2)++last),final;split;[|split;[reflexivity|exact POST]].
  eapply library_steps_trans.
  - apply original_runs_preserved;eapply store_path_actual.
    replace 6%nat with (4+2)%nat by reflexivity;eapply store_path_trans;[exact PATH|].
    eapply store_next;[exact OLD|apply unchanged_store_edge;WriteAll.structural|].
    eapply store_next;[exact OLD|apply finish_send_source|]. constructor;exact OLD.
  - eapply library_steps_trans.
    + exact (plug_library_steps result_ge cell _ _ _ (finish_sender_cont local (finish_temps input ofs) Kstop) I SEND).
    + eapply library_steps_trans;[|exact TAIL].
      apply original_runs_preserved;eapply store_path_actual.
      eapply store_next;[exact AFTER|apply unchanged_store_edge;WriteAll.structural|].
      eapply store_next;[exact AFTER|apply unchanged_store_edge;WriteAll.structural|]. constructor;exact AFTER.
Qed.
