(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-library.machine: Universal old-proof reuse in the enlarged transition system. *)
From Coq Require Import List Lia.
From compcert Require Import AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Slice IO Machine ClightSteps WriteMemory WriteAll Deterministic ErrorNumber Readers
  StoreSteps WriteBytes Writers Library LibraryMachine.
Import ListNotations.

Definition original_boundary s := internal_state s \/
  (exists op args k m, s = Callstate
    (External (io_function op) [tint; tptr tvoid; tulong] tlong cc_default) args k m) \/
  (exists k m, s = Callstate (External errno_function [] (tptr tint) cc_default) [] k m).

Lemma original_boundary_exact : forall ge cell s ev target,
  original_boundary s -> library_step ge cell (live s) ev target ->
  exists original, ev = original_event original /\ Machine.step ge cell (live s) original target.
Proof.
  intros ge cell s ev target BOUND STEP.
  destruct BOUND as [IN|[[op [args [k [m EQ]]]]|[k [m EQ]]]].
  - eapply internal_boundary_unchanged; eassumption.
  - subst s; destruct op; inversion STEP; subst; eauto;
      match goal with H : library_ready _ _ |- _ => inversion H end.
  - subst s; inversion STEP; subst; eauto;
      match goal with H : library_ready _ _ |- _ => inversion H end.
Qed.

Lemma library_dead_steps : forall ge cell m events target,
  library_steps ge cell (dead m) events target -> events = [] /\ target = dead m.
Proof.
  intros ge cell m events target RUN; inversion RUN; subst; auto.
  exfalso; eapply library_dead_cannot_resume; eassumption.
Qed.

Theorem store_path_library_projection : forall ge cell P start count value final,
  store_path ge P start count (Returnstate value Kstop final) ->
  forall events target, library_steps ge cell (live start) events target ->
  exists original, events = map original_event original /\
    Machine.steps ge cell (live start) original target.
Proof.
  intros ge cell P start count value final PATH events target RUN.
  remember (live start) as initial eqn:INIT. revert start count INIT PATH.
  induction RUN as [s|s ev mid events target STEP RUN IH]; intros start count INIT PATH; subst s.
  - exists []; split; [reflexivity|constructor].
  - inversion PATH as [s GOOD|s next n last GOOD EDGE TAIL]; subst.
    + destruct (original_boundary_exact ge cell (Returnstate value Kstop final) ev mid (or_introl I) STEP) as [old [EV OLD]]; subst ev.
      destruct (returned_step _ _ _ _ _ _ OLD) as [EV TARGET]; subst.
      destruct (library_dead_steps _ _ _ _ _ RUN) as [ES TARGET]; subst.
      exists [loss_step]; split; [reflexivity|econstructor; [exact OLD|constructor]].
    + pose proof EDGE as [IN _].
      destruct (original_boundary_exact _ _ _ _ _ (or_introl IN) STEP) as [old [EV OLD]]; subst ev.
      destruct (store_edge_cases _ _ _ _ _ _ EDGE OLD) as [[EV TARGET]|[EV TARGET]]; subst.
      * destruct (IH _ _ eq_refl TAIL) as [rest [ES ORIGINAL]]; subst.
        exists (source_step E0 :: rest); split; [reflexivity|econstructor; eassumption].
      * destruct (library_dead_steps _ _ _ _ _ RUN) as [ES TARGET]; subst.
        exists [loss_step]; split; [reflexivity|econstructor; [exact OLD|constructor]].
Qed.

Lemma certain_original_boundary : forall ge cell s ev next,
  certain_step ge cell s ev next -> original_boundary s.
Proof.
  intros ge cell s ev next [ORD [REAL _]]. destruct ORD as [EV|EV]; subst;
    inversion REAL; subst.
  - left; assumption.
  - right; right; eauto.
Qed.

Theorem execution_library_projection : forall ge cell start schedule value final,
  execution ge cell start schedule (Returnstate value Kstop final) ->
  forall events target, library_steps ge cell (live start) events target ->
  exists original, events = map original_event original /\
    Machine.steps ge cell (live start) original target.
Proof.
  intros ge cell start schedule value final SCRIPT events target RUN.
  remember (live start) as initial eqn:INIT. revert start schedule INIT SCRIPT.
  induction RUN as [s|s ev mid events target STEP RUN IH]; intros start schedule INIT SCRIPT; subst s.
  - exists []; split; [reflexivity|constructor].
  - inversion SCRIPT as [|s event next rest last CERT TAIL]; subst.
    + destruct (original_boundary_exact ge cell (Returnstate value Kstop final) ev mid (or_introl I) STEP) as [old [EV OLD]]; subst ev.
      destruct (returned_step _ _ _ _ _ _ OLD) as [EV TARGET]; subst.
      destruct (library_dead_steps _ _ _ _ _ RUN) as [ES TARGET]; subst.
      exists [loss_step]; split; [reflexivity|econstructor; [exact OLD|constructor]].
    + destruct (original_boundary_exact _ _ _ _ _ (certain_original_boundary _ _ _ _ _ CERT) STEP)
        as [old [EV OLD]]; subst ev.
      destruct CERT as [_ [_ [_ UNIQUE]]].
      destruct (UNIQUE _ _ OLD) as [[EV TARGET]|[EV TARGET]]; subst.
      * destruct (IH _ _ eq_refl TAIL) as [suffix [ES ORIGINAL]]; subst.
        exists (event :: suffix); split; [reflexivity|econstructor; eassumption].
      * destruct (library_dead_steps _ _ _ _ _ RUN) as [ES TARGET]; subst.
        exists [loss_step]; split; [reflexivity|econstructor; [exact OLD|constructor]].
Qed.

Lemma write_all_original_boundary : forall ge q input done last s,
  WriteAll.invariant ge q input done last (live s) -> original_boundary s.
Proof.
  intros ge q input done last s INV. inversion INV; subst.
  match goal with H : routed _ _ _ _ _ _ |- _ => destruct H as [final [PATH END]] end.
  inversion PATH; subst.
  - inversion END; subst.
    + right; left. unfold write_state. eauto.
    + right; right. unfold errno_state. eauto.
    + left; exact I.
    + left; exact I.
  - left. destruct H as [IN _]; exact IN.
Qed.

Theorem write_all_library_invariant_projection : forall ge q input s events target,
  library_steps ge (cell_of q) s events target -> symbols ge ->
  forall done last, WriteAll.invariant ge q input done last s ->
  exists original, events = map original_event original /\ Machine.steps ge (cell_of q) s original target.
Proof.
  intros ge q input s events target RUN; induction RUN; intros SYM done previous INV.
  - exists []; split; [reflexivity|constructor].
  - destruct s as [s|m].
    2: { exfalso; eapply library_dead_cannot_resume; exact H. }
    destruct (original_boundary_exact _ _ _ _ _ (write_all_original_boundary _ _ _ _ _ _ INV) H)
      as [old [EV OLD]]; subst ev.
    pose proof (write_all_invariant_step _ _ _ _ _ _ _ _ SYM INV OLD) as NEXT.
    destruct (IHRUN SYM _ _ NEXT) as [tail [ES ORIGINAL]]; subst.
    exists (old :: tail); split; [reflexivity|econstructor; eassumption].
Qed.

Theorem write_all_library_projection : forall q input m events target,
  write_owned q input m ->
  library_steps (Clight.globalenv Slice.prog) (cell_of q)
    (live (WriteAll.initial_state q m)) events target ->
  exists original, events = map original_event original /\
    Machine.steps (Clight.globalenv Slice.prog) (cell_of q)
      (live (WriteAll.initial_state q m)) original target.
Proof.
  intros q input m events target OWN RUN.
  eapply write_all_library_invariant_projection; [exact RUN|exact actual_program_symbols|].
  apply invariant_initial; [exact actual_program_symbols|exact OWN].
Qed.

Theorem writer_library_prefix_safety : forall cell m b ofs f value values count events target,
  writer_input m b ofs f value values count ->
  library_steps (Clight.globalenv Slice.prog) cell
    (live (writer_initial f b ofs value Kstop m)) events target ->
  writer_prefix m b (Integers.Ptrofs.unsigned ofs) values (routine_memory target) /\
    length events <= S count.
Proof.
  intros cell m b ofs f value values count events target INPUT RUN.
  destruct (writer_execution (Clight.globalenv Slice.prog) _ _ _ _ _ _ _ Kstop INPUT I)
    as [final [_ PATH]].
  destruct (store_path_library_projection _ _ _ _ _ _ _ PATH _ _ RUN) as [original [ES ORIGINAL]].
  subst. rewrite map_length. eapply writer_all_prefixes; eassumption.
Qed.

Theorem reader_library_return_exact : forall cell m b ofs f value count events actual after,
  reader_input m b ofs f value count ->
  library_steps (Clight.globalenv Slice.prog) cell (live (Readers.initial f b ofs Kstop m)) events
    (live (Returnstate actual Kstop after)) ->
  actual = value /\ after = m /\
    events = map original_event (repeat (source_step E0) count).
Proof.
  intros cell m b ofs f value count events actual after INPUT RUN.
  pose proof (reader_execution (Clight.globalenv Slice.prog) cell _ _ _ _ _ _ Kstop INPUT) as SCRIPT.
  destruct (execution_library_projection _ _ _ _ _ _ SCRIPT _ _ RUN) as [original [ES ORIGINAL]].
  destruct (reader_return_exact _ _ _ _ _ _ _ _ _ _ INPUT ORIGINAL) as [A [M EVENTS]].
  subst; auto.
Qed.
