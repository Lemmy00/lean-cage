(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Split actual caller executions at checked native numeric procedure returns. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine Deterministic ClightSteps StoreSteps.
From EntryNative Require Import EntrySource NativeArguments NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine.
From LeanCageMainNumber Require Import NumberStructure NumberMath NumberMemory NumberStorage NumberSource.
Import ListNotations.
Open Scope Z_scope.

Definition process_source_event := process_entry (entry_library (LibraryMachine.original_event (source_step E0))).

Theorem process_steps_append ge cell before prefix middle suffix after :
  process_steps ge cell before prefix middle -> process_steps ge cell middle suffix after ->
  process_steps ge cell before (prefix++suffix) after.
Proof. intros PREFIX SUFFIX;induction PREFIX;cbn;eauto using process_steps_cons. Qed.

Theorem process_steps_split ge cell before prefix suffix after :
  process_steps ge cell before (prefix++suffix) after ->
  exists middle, process_steps ge cell before prefix middle /\
    process_steps ge cell middle suffix after.
Proof.
  revert before;induction prefix as [|event rest IH];intros before RUN;cbn in RUN.
  - exists before;split;[constructor|exact RUN].
  - inversion RUN as [|first current next tail last STEP TAIL];subst.
    destruct (IH _ TAIL) as [middle [PREFIX SUFFIX]].
    exists middle;split;[econstructor;eassumption|exact SUFFIX].
Qed.

Theorem process_store_path_actual ge cell (P : mem -> Prop) start count last :
  store_path ge P start count last ->
  process_steps ge cell (live start) (repeat process_source_event count) (live last).
Proof.
  intro PATH. induction PATH; cbn; [constructor|].
  econstructor; [|exact IHPATH].
  apply process_entry_step, entry_library_step, LibraryMachine.original_step.
  apply internal; destruct H0 as [IN [STEP REST]]; assumption.
Qed.

Theorem process_store_path_decomposition ge cell (P : mem -> Prop) start count last :
  store_path ge P start count last ->
  forall events target, process_steps ge cell (live start) events target ->
  (exists rest, events = repeat process_source_event count ++ rest /\
    process_steps ge cell (live last) rest target) \/
  (exists used current remaining, (count = used + remaining)%nat /\
    events = repeat process_source_event used /\ target = live current /\
    store_path ge P current remaining last) \/
  (exists used memory, (used < count)%nat /\
    events = repeat process_source_event used ++
      [process_entry (entry_library (LibraryMachine.original_event loss_step))] /\
    target = dead memory /\ P memory).
Proof.
  intro SCRIPT; induction SCRIPT as [state GOOD|state next count last GOOD EDGE SCRIPT IH];
    intros events target RUN.
  - left; exists events; cbn; auto.
  - destruct events as [|event rest].
    + inversion RUN; subst. right; left. exists 0%nat, state, (S count); cbn.
      repeat split; auto. econstructor; eassumption.
    + inversion RUN; subst.
      match goal with STEP : process_step _ _ _ _ _ |- _ =>
        destruct (process_store_edge_cases _ _ _ _ _ _ EDGE STEP)
          as [[EVENT TARGET]|[EVENT TARGET]] end; subst.
      * match goal with TAIL : process_steps _ _ (live next) _ _ |- _ =>
          destruct (IH _ _ TAIL) as [[suffix [EVENTS TAILRUN]]|
            [[used [current [remaining [COUNT [EVENTS [TARGET PATH]]]]]]|
             [used [memory [COUNT [EVENTS [TARGET PM]]]]]]] end.
        -- left; exists suffix; cbn; split; [rewrite EVENTS; reflexivity|exact TAILRUN].
        -- right; left; exists (S used), current, remaining; cbn.
           split; [lia|]. split; [rewrite EVENTS; reflexivity|]. auto.
        -- right; right; exists (S used), memory; cbn.
           split; [lia|]. split; [rewrite EVENTS; reflexivity|]. auto.
      * match goal with TAIL : process_steps _ _ (dead _) _ _ |- _ =>
          destruct (process_dead_steps _ _ _ _ _ TAIL) as [EVENTS TARGET'] end; subst.
        right; right; exists 0%nat, (memory_of state); cbn; auto with arith.
Qed.

Theorem current_number_process_path ge cell before input offset bytes output outoffset k :
  number_input before input offset bytes -> number_output before output outoffset ->
  exists count after,
    number_post before output outoffset (decimal_number bytes) after /\
    process_steps ge cell
      (live (Callstate (Internal EntrySource.f_number)
        [Vptr input offset; Vptr output outoffset] k before))
      (repeat process_source_event count)
      (live (Returnstate (number_code (decimal_number bytes)) (call_cont k) after)) /\
    forall events target,
      process_steps ge cell
        (live (Callstate (Internal EntrySource.f_number)
          [Vptr input offset; Vptr output outoffset] k before)) events target ->
      (exists rest, events = repeat process_source_event count ++ rest /\
        process_steps ge cell
          (live (Returnstate (number_code (decimal_number bytes)) (call_cont k) after)) rest target) \/
      (exists used current remaining, (count = used + remaining)%nat /\
        events = repeat process_source_event used /\ target = live current /\
        store_path ge (number_memory before output outoffset (decimal_number bytes)) current remaining
          (Returnstate (number_code (decimal_number bytes)) (call_cont k) after)) \/
      (exists used memory, (used < count)%nat /\
        events = repeat process_source_event used ++
          [process_entry (entry_library (LibraryMachine.original_event loss_step))] /\
        target = dead memory /\ number_memory before output outoffset (decimal_number bytes) memory).
Proof.
  intros INPUT OUTPUT. rewrite current_entry_number_exact.
  destruct (number_source_path ge before input offset bytes output outoffset k INPUT OUTPUT)
    as [count [after [POST PATH]]].
  exists count, after; split; [exact POST|]. split.
  - eapply process_store_path_actual; exact PATH.
  - intros events target RUN. eapply process_store_path_decomposition; eassumption.
Qed.
