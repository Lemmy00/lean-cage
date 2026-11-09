(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Reuse deterministic errno effects in the larger process machine. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Clight.
Require Import Machine Deterministic LibraryMachine LibraryPreservation.
From EntryNative Require Import NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessCalls.

Theorem process_certain_step_cases ge cell state event next actual target :
  certain_step ge cell state event next ->process_step ge cell(live state)actual target ->
  (actual=process_entry(entry_library(original_event event)) /\target=live next) \/
  (actual=process_entry(entry_library(original_event loss_step)) /\target=dead(memory_of state)).
Proof.
  intros CERT STEP.
  destruct(process_original_boundary_exact _ _ _ _ _
    (certain_original_boundary _ _ _ _ _ CERT)STEP)as[original[EVENT REAL]].
  subst actual;destruct CERT as[_[_[_ CASES]]].
  destruct(CASES _ _ REAL)as[[EVENT TARGET]|[EVENT TARGET]];subst;auto.
Qed.
