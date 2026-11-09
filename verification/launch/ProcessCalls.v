(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Reuse checked numeric/write source procedures in the process machine. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import IO Machine ClightSteps StoreSteps WriteMemory WriteAll LibraryMachine LibraryPreservation.
From EntryNative Require Import EntrySource NativeHandoffMachine NativeHandoffBindings.
From EntryProcess Require Import ProcessMachine.
Import ListNotations.
Open Scope Z_scope.

Lemma entry_original_boundary_exact ge cell state event after :
  original_boundary state -> entry_handoff_step ge cell (live state) event after ->
  exists original, event = entry_library (original_event original) /\
    Machine.step ge cell (live state) original after.
Proof.
  intros BOUND STEP. pose proof BOUND as ORIGINAL.
  destruct BOUND as [IN|[[op [args [k [m SAME]]]]|[k [m SAME]]]].
  - eapply entry_internal_step_exact; eassumption.
  - subst state; destruct op; inversion STEP; subst;
      destruct (original_boundary_exact _ _ _ _ _ ORIGINAL H)
        as [original [EVENT REAL]]; subst; eauto.
  - subst state; inversion STEP; subst.
    destruct (original_boundary_exact _ _ _ _ _ ORIGINAL H)
      as [original [EVENT REAL]]; subst; eauto.
Qed.

Lemma process_original_boundary_exact ge cell state event after :
  original_boundary state -> process_step ge cell (live state) event after ->
  exists original, event = process_entry (entry_library (original_event original)) /\
    Machine.step ge cell (live state) original after.
Proof.
  intros BOUND STEP. pose proof BOUND as ORIGINAL.
  destruct BOUND as [IN|[[op [args [k [m SAME]]]]|[k [m SAME]]]].
  - eapply process_internal_step_exact; eassumption.
  - subst state; destruct op; inversion STEP; subst;
      destruct (entry_original_boundary_exact _ _ _ _ _ ORIGINAL H)
        as [original [EVENT REAL]]; subst; eauto.
  - subst state; inversion STEP; subst.
    destruct (entry_original_boundary_exact _ _ _ _ _ ORIGINAL H)
      as [original [EVENT REAL]]; subst; eauto.
Qed.

Theorem process_write_invariant_projection ge q input state events target :
  process_steps ge (cell_of q) state events target -> WriteAll.symbols ge ->
  forall done last, WriteAll.invariant ge q input done last state ->
  exists original, events = map (fun event => process_entry (entry_library (original_event event))) original /\
    Machine.steps ge (cell_of q) state original target.
Proof.
  intro RUN; induction RUN; intros SYMBOLS done previous INV.
  - exists []; split; [reflexivity|constructor].
  - destruct before as [state|memory].
    2: { exfalso; eapply process_dead_cannot_resume; eassumption. }
    destruct (process_original_boundary_exact _ _ _ _ _
      (write_all_original_boundary _ _ _ _ _ _ INV) H) as [original [EVENT REAL]].
    subst event.
    pose proof (write_all_invariant_step _ _ _ _ _ _ _ _ SYMBOLS INV REAL) as NEXT.
    destruct (IHRUN SYMBOLS _ _ NEXT) as [suffix [EVENTS TAIL]].
    subst. exists (original :: suffix); split; [reflexivity|econstructor; eassumption].
Qed.

Theorem current_write_symbols : WriteAll.symbols (Clight.globalenv EntrySource.prog).
Proof. split; eexists; split; vm_compute; reflexivity. Qed.

Local Opaque EntrySource.prog.

Theorem current_write_process_return q input before events value after :
  write_owned q input before ->
  process_steps (Clight.globalenv EntrySource.prog) (cell_of q)
    (live (Callstate (Internal EntrySource.f_write_all)
      [Vint (descriptor q); Vptr (buffer_block q) (Ptrofs.repr (buffer_offset q));
       Vlong (Int64.repr (requested q))] Kstop before)) events
    (live (Returnstate value Kstop after)) ->
  exists original,
    events = map (fun event => process_entry (entry_library (original_event event))) original /\
    write_owned q input after /\
    ((value = Vint Int.zero /\ emitted_trace original = input) \/
     (value = Vint Int.mone /\ failed_reply (fold_left last_update original None) /\
      emitted_trace original <> input)).
Proof.
  intros OWN RUN. rewrite current_entry_write_all_exact in RUN.
  change (process_steps (Clight.globalenv EntrySource.prog) (cell_of q)
    (live (WriteAll.initial_state q before)) events (live (Returnstate value Kstop after))) in RUN.
  destruct (process_write_invariant_projection _ _ _ _ _ _ RUN current_write_symbols [] None
    (invariant_initial _ _ _ _ current_write_symbols OWN)) as [original [EVENTS REAL]].
  pose proof (write_all_invariant_runs _ _ _ _ _ _ REAL current_write_symbols [] None
    (invariant_initial _ _ _ _ current_write_symbols OWN)) as INV.
  exists original; split; [exact EVENTS|].
  pose proof (proj1 (invariant_facts _ _ _ _ _ _ INV)) as PRESERVED.
  split; [exact PRESERVED|].
  inversion INV; subst.
  match goal with H : routed _ _ _ _ _ _ |- _ => destruct H as [final [PATH END]] end.
  apply terminal_path in PATH; subst final. inversion END; subst; cbn in *.
  - left; auto.
  - right; split; [reflexivity|]. split; [assumption|].
    intro SAME. apply (f_equal (@List.length Byte.int)) in SAME.
    rewrite app_length in SAME. destruct rest; [contradiction|cbn in SAME; lia].
Qed.
