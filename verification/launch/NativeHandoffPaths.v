(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Preserve the real caller continuation across the checked numeric callee. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine Deterministic ClightSteps StoreSteps.
From EntryNative Require Import EntrySource NativeArguments NativeHandoffMachine.
From LeanCageMainNumber Require Import NumberStructure NumberMath NumberMemory NumberStorage NumberSource.
Import ListNotations.
Open Scope Z_scope.

(* A nonterminal endpoint may resume its caller.  In contrast to the Kstop
   theorem, this result splits the actual execution at that endpoint and makes
   no assertion about the caller's subsequent return state. *)
Theorem handoff_store_path_decomposition ge cell (P : mem -> Prop) start count last :
  store_path ge P start count last ->
  forall events target, steps ge cell (live start) events target ->
  (exists rest,
    events = repeat (source_step E0) count ++ rest /\
    steps ge cell (live last) rest target) \/
  (exists used current remaining,
    (count = used + remaining)%nat /\
    events = repeat (source_step E0) used /\ target = live current /\
    store_path ge P current remaining last) \/
  (exists used m,
    (used < count)%nat /\
    events = repeat (source_step E0) used ++ [loss_step] /\
    target = dead m /\ P m).
Proof.
  intros SCRIPT; induction SCRIPT as [s GOOD|s next count last GOOD EDGE SCRIPT IH];
    intros events target RUN.
  - left; exists events; cbn; auto.
  - destruct events as [|ev rest].
    + inversion RUN; subst. right; left.
      exists 0%nat, s, (S count); cbn; repeat split; auto.
      econstructor; eassumption.
    + inversion RUN; subst.
      match goal with STEP : step _ _ _ _ _ |- _ =>
        destruct (store_edge_cases _ _ _ _ _ _ EDGE STEP)
          as [[EVENT TARGET]|[EVENT TARGET]] end; subst.
      * match goal with TAIL : steps _ _ (live next) _ _ |- _ =>
          destruct (IH _ _ TAIL)
            as [[suffix [EVENTS TAILRUN]]|
                [[used [current [remaining [COUNT [EVENTS [TARGET PATH]]]]]]|
                 [used [m [COUNT [EVENTS [TARGET PM]]]]]]] end.
        -- left; exists suffix; cbn; split; [rewrite EVENTS; reflexivity|exact TAILRUN].
        -- right; left; exists (S used), current, remaining; cbn.
           split; [lia|]. split; [rewrite EVENTS; reflexivity|]. auto.
        -- right; right; exists (S used), m; cbn.
           split; [lia|]. split; [rewrite EVENTS; reflexivity|]. auto.
      * match goal with TAIL : steps _ _ (dead _) _ _ |- _ =>
          destruct (dead_steps _ _ _ _ _ TAIL) as [EVENTS TARGET'] end; subst.
        right; right; exists 0%nat, (memory_of s); cbn; auto with arith.
Qed.

Definition handoff_source_event := entry_library (LibraryMachine.original_event (source_step E0)).

Theorem handoff_entry_path_decomposition ge cell (P : mem -> Prop) start count last :
  store_path ge P start count last ->
  forall events target, entry_handoff_steps ge cell (live start) events target ->
  (exists rest,
    events = repeat handoff_source_event count ++ rest /\
    entry_handoff_steps ge cell (live last) rest target) \/
  (exists used current remaining,
    (count = used + remaining)%nat /\
    events = repeat handoff_source_event used /\ target = live current /\
    store_path ge P current remaining last) \/
  (exists used m,
    (used < count)%nat /\
    events = repeat handoff_source_event used ++
      [entry_library (LibraryMachine.original_event loss_step)] /\
    target = dead m /\ P m).
Proof.
  intros SCRIPT; induction SCRIPT as [s GOOD|s next count last GOOD EDGE SCRIPT IH];
    intros events target RUN.
  - left; exists events; cbn; auto.
  - destruct events as [|ev rest].
    + inversion RUN; subst. right; left.
      exists 0%nat, s, (S count); cbn; repeat split; auto.
      econstructor; eassumption.
    + inversion RUN; subst.
      match goal with STEP : entry_handoff_step _ _ _ _ _ |- _ =>
        destruct (entry_store_edge_cases _ _ _ _ _ _ EDGE STEP)
          as [[EVENT TARGET]|[EVENT TARGET]] end; subst.
      * match goal with TAIL : entry_handoff_steps _ _ (live next) _ _ |- _ =>
          destruct (IH _ _ TAIL)
            as [[suffix [EVENTS TAILRUN]]|
                [[used [current [remaining [COUNT [EVENTS [TARGET PATH]]]]]]|
                 [used [m [COUNT [EVENTS [TARGET PM]]]]]]] end.
        -- left; exists suffix; cbn; split; [rewrite EVENTS; reflexivity|exact TAILRUN].
        -- right; left; exists (S used), current, remaining; cbn.
           split; [lia|]. split; [rewrite EVENTS; reflexivity|]. auto.
        -- right; right; exists (S used), m; cbn.
           split; [lia|]. split; [rewrite EVENTS; reflexivity|]. auto.
      * match goal with TAIL : entry_handoff_steps _ _ (dead _) _ _ |- _ =>
          destruct (entry_handoff_dead_steps _ _ _ _ _ TAIL) as [EVENTS TARGET'] end; subst.
        right; right; exists 0%nat, (memory_of s); cbn; auto with arith.
Qed.

Theorem handoff_store_path_reached ge cell (P : mem -> Prop) start count last events target :
  store_path ge P start count last ->
  steps ge cell (live start) events target ->
  (count <= length events)%nat ->
  (exists rest,
    events = repeat (source_step E0) count ++ rest /\
    steps ge cell (live last) rest target) \/
  (exists used m,
    (used < count)%nat /\
    events = repeat (source_step E0) used ++ [loss_step] /\
    target = dead m /\ P m).
Proof.
  intros SCRIPT RUN LENGTH.
  destruct (handoff_store_path_decomposition _ _ _ _ _ _ SCRIPT _ _ RUN)
    as [DONE|[[used [current [remaining [COUNT [EVENTS [TARGET PATH]]]]]]|LOST]];
    [auto| |auto].
  subst events target. rewrite repeat_length in LENGTH.
  assert (remaining = 0%nat) by lia; subst remaining.
  inversion PATH; subst. left; exists []; rewrite app_nil_r, Nat.add_0_r.
  split; [reflexivity|constructor].
Qed.

Theorem current_entry_number_caller_path ge cell before input offset bytes output outoffset k :
  number_input before input offset bytes -> number_output before output outoffset ->
  exists count after,
    number_post before output outoffset (decimal_number bytes) after /\
    steps ge cell
      (live (Callstate (Internal EntrySource.f_number)
        [Vptr input offset; Vptr output outoffset] k before))
      (repeat (source_step E0) count)
      (live (Returnstate (number_code (decimal_number bytes)) (call_cont k) after)) /\
    (forall events target,
      steps ge cell
        (live (Callstate (Internal EntrySource.f_number)
          [Vptr input offset; Vptr output outoffset] k before)) events target ->
      (count <= length events)%nat ->
      (exists rest,
        events = repeat (source_step E0) count ++ rest /\
        steps ge cell
          (live (Returnstate (number_code (decimal_number bytes)) (call_cont k) after))
          rest target) \/
      (exists used m,
        (used < count)%nat /\
        events = repeat (source_step E0) used ++ [loss_step] /\
        target = dead m /\ number_memory before output outoffset (decimal_number bytes) m)).
Proof.
  intros INPUT OUTPUT.
  rewrite current_entry_number_exact.
  destruct (number_source_path ge before input offset bytes output outoffset k INPUT OUTPUT)
    as [count [after [POST PATH]]].
  exists count, after; split; [exact POST|]. split.
  - eapply store_path_actual; exact PATH.
  - intros events target RUN LENGTH; eapply handoff_store_path_reached; eassumption.
Qed.

Theorem handoff_entry_path_reached ge cell (P : mem -> Prop) start count last events target :
  store_path ge P start count last ->
  entry_handoff_steps ge cell (live start) events target ->
  (count <= length events)%nat ->
  (exists rest,
    events = repeat handoff_source_event count ++ rest /\
    entry_handoff_steps ge cell (live last) rest target) \/
  (exists used m,
    (used < count)%nat /\
    events = repeat handoff_source_event used ++
      [entry_library (LibraryMachine.original_event loss_step)] /\
    target = dead m /\ P m).
Proof.
  intros SCRIPT RUN LENGTH.
  destruct (handoff_entry_path_decomposition _ _ _ _ _ _ SCRIPT _ _ RUN)
    as [DONE|[[used [current [remaining [COUNT [EVENTS [TARGET PATH]]]]]]|LOST]];
    [auto| |auto].
  subst events target; rewrite repeat_length in LENGTH.
  assert (remaining = 0%nat) by lia; subst remaining.
  inversion PATH; subst; left; exists []; rewrite app_nil_r, Nat.add_0_r.
  split; [reflexivity|constructor].
Qed.

Theorem current_entry_number_entry_path ge cell before input offset bytes output outoffset k :
  number_input before input offset bytes -> number_output before output outoffset ->
  exists count after,
    number_post before output outoffset (decimal_number bytes) after /\
    entry_handoff_steps ge cell
      (live (Callstate (Internal EntrySource.f_number)
        [Vptr input offset; Vptr output outoffset] k before))
      (repeat handoff_source_event count)
      (live (Returnstate (number_code (decimal_number bytes)) (call_cont k) after)) /\
    (forall events target,
      entry_handoff_steps ge cell
        (live (Callstate (Internal EntrySource.f_number)
          [Vptr input offset; Vptr output outoffset] k before)) events target ->
      (count <= length events)%nat ->
      (exists rest,
        events = repeat handoff_source_event count ++ rest /\
        entry_handoff_steps ge cell
          (live (Returnstate (number_code (decimal_number bytes)) (call_cont k) after)) rest target) \/
      (exists used m,
        (used < count)%nat /\
        events = repeat handoff_source_event used ++
          [entry_library (LibraryMachine.original_event loss_step)] /\
        target = dead m /\ number_memory before output outoffset (decimal_number bytes) m)).
Proof.
  intros INPUT OUTPUT; rewrite current_entry_number_exact.
  destruct (number_source_path ge before input offset bytes output outoffset k INPUT OUTPUT)
    as [count [after [POST PATH]]].
  exists count,after; split; [exact POST|]. split.
  - pose proof (entry_original_steps_preserved _ cell _ _ _ (store_path_actual _ cell _ _ _ _ PATH)) as RUN.
    rewrite map_repeat in RUN; exact RUN.
  - intros events target RUN LENGTH; eapply handoff_entry_path_reached; eassumption.
Qed.
