(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.memory: Every write_all source prefix changes only the actual TLS error cell. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Clight.
Require Import Slice IO Machine Deterministic ClightSteps WriteBytes WriteMemory WriteAll LibraryMachine LibraryPreservation ProcessEffects.
Import ListNotations.
Open Scope Z_scope.
Inductive tls_history cell : mem -> mem -> Prop :=
| tls_history_refl : forall m,tls_history cell m m
| tls_history_store : forall m mid after value,
    Mem.store Mint32 m (tls_block cell) (tls_offset cell) (Vint value)=Some mid ->
    tls_history cell mid after -> tls_history cell m after.
Lemma tls_history_trans : forall cell a b c,
  tls_history cell a b -> tls_history cell b c -> tls_history cell a c.
Proof. intros cell a b c AB;induction AB;intros BC;[exact BC|econstructor;eauto]. Qed.
Lemma errno_history : forall q m error after,
  errno_change q m error after -> tls_history (cell_of q) m after.
Proof. intros q m error after CHANGE;inversion CHANGE;subst;[constructor|econstructor;[exact H|constructor]]. Qed.

Theorem tls_history_outside : forall cell m after,
  tls_history cell m after -> Mem.unchanged_on (outside_bytes (tls_block cell) (tls_offset cell) 4) m after.
Proof.
  intros cell m after HISTORY;induction HISTORY;[apply Mem.unchanged_on_refl|].
  eapply Mem.unchanged_on_trans;[|exact IHHISTORY].
  eapply Mem.store_unchanged_on;[exact H|]. unfold outside_bytes;cbn;intros pos RANGE [NE|[LOW|HIGH]];lia.
Qed.
Theorem tls_history_permissions : forall cell m after,
  tls_history cell m after -> forall b pos kind permission,
    Mem.perm after b pos kind permission <-> Mem.perm m b pos kind permission.
Proof.
  intros cell m after HISTORY;induction HISTORY;intros;[tauto|].
  rewrite IHHISTORY;split;[eapply Mem.perm_store_2|eapply Mem.perm_store_1];eassumption.
Qed.
Theorem tls_history_ready : forall cell m after,
  tls_history cell m after -> tls_ready cell m -> tls_ready cell after.
Proof.
  intros cell m after HISTORY [LOW [HIGH [PERMS ALIGN]]];split;[exact LOW|]. split;[exact HIGH|].
  split;[|exact ALIGN]. intros pos RANGE;apply (tls_history_permissions _ _ _ HISTORY);apply PERMS;exact RANGE.
Qed.

Lemma write_effect_history : forall q sent m reply after,
  io_return (suffix q sent) m reply after -> tls_history (cell_of q) m after.
Proof.
  intros q sent m reply after EFFECT;inversion EFFECT;subst;cbn [operation suffix] in *;try discriminate.
  all: eapply (errno_history q);eapply suffix_errno;eassumption.
Qed.

Lemma write_endpoint_history : forall ge q input done last s ev target,
  endpoint q input done last s -> Machine.step ge (cell_of q) (live s) ev target ->
  tls_history (cell_of q) (memory_of s) (machine_memory target).
Proof.
  intros ge q input done last s ev target END STEP.
  inversion END as [rest le m EQ NE OWN REGS|rest le m error EQ NE OWN REGS N LAST LOAD|
    m EQ OWN|rest m EQ NE OWN FAIL];subst s.
  - assert (SUFFIX : owned (suffix q (Z.of_nat (length done))) m).
    { apply suffix_owned with (rest:=rest);[rewrite <- EQ;exact OWN|exact NE]. }
    destruct (write_machine_cases _ _ _ _ _ _ _ SUFFIX STEP)
      as [[reply [after [EFFECT [EVENT TARGET]]]]|[[EVENT TARGET]|[[EVENT TARGET]|[bytes [error [after [EFFECT [EVENT TARGET]]]]]]]];
      subst ev target;cbn [memory_of machine_memory];try apply tls_history_refl;
      eapply write_effect_history;exact EFFECT.
  - destruct (errno_machine_cases _ _ _ _ _ _ STEP) as [[EVENT TARGET]|[EVENT TARGET]];
      subst ev target;constructor.
  - destruct (terminal_machine_cases _ _ _ _ _ _ STEP) as [EVENT TARGET];subst ev target;constructor.
  - destruct (terminal_machine_cases _ _ _ _ _ _ STEP) as [EVENT TARGET];subst ev target;constructor.
Qed.

Lemma write_invariant_history_step : forall ge q input done last s ev target,
  invariant ge q input done last s -> Machine.step ge (cell_of q) s ev target ->
  tls_history (cell_of q) (machine_memory s) (machine_memory target).
Proof.
  intros ge q input done last s ev target INV STEP.
  inversion INV as [live_s [final [PATH END]]|m rest EQ OWN];subst s;[|inversion STEP].
  inversion PATH as [|a mid b EDGE REST];subst.
  - eapply write_endpoint_history;[exact END|exact STEP].
  - destruct (machine_edge_cases _ _ _ _ _ _ EDGE STEP) as [[EVENT TARGET]|[EVENT TARGET]];subst.
    + destruct EDGE as [_ [_ [MEM _]]];cbn [machine_memory];rewrite MEM;constructor.
    + constructor.
Qed.

Theorem write_invariant_history : forall ge q input s events target,
  symbols ge -> Machine.steps ge (cell_of q) s events target ->
  forall done last,invariant ge q input done last s ->
    tls_history (cell_of q) (machine_memory s) (machine_memory target).
Proof.
  intros ge q input s events target SYMBOLS RUN;induction RUN;intros done last_reply INV.
  - constructor.
  - eapply tls_history_trans.
    + eapply write_invariant_history_step;[exact INV|exact H].
    + apply (IHRUN (done++emitted e) (last_update last_reply e)).
      eapply write_all_invariant_step;[exact SYMBOLS|exact INV|exact H].
Qed.

Theorem write_all_tls_history : forall q input m events target,
  write_owned q input m ->
  library_steps (Clight.globalenv Slice.prog) (cell_of q) (live (WriteAll.initial_state q m)) events target ->
  tls_history (cell_of q) m (routine_memory target).
Proof.
  intros q input m events target OWN RUN.
  destruct (write_all_library_projection _ _ _ _ _ OWN RUN) as [old [ES ORIGINAL]].
  change (tls_history (cell_of q) (machine_memory (live (WriteAll.initial_state q m))) (machine_memory target)).
  eapply write_invariant_history;[apply actual_program_symbols|exact ORIGINAL|].
  apply invariant_initial;[apply actual_program_symbols|exact OWN].
Qed.
