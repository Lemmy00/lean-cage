(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Single-operation channel, descriptor, mask and fork source boundaries. *)
From Stdlib Require Import ZArith List String.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import IO Machine ClightSteps StoreSteps LibraryMachine.
From EntryNative Require Import NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine.
Import ListNotations.
Open Scope Z_scope.

Definition namespace_pair_definition : Clight.fundef := External
  (EF_external "socketpair" (mksignature [Xint; Xint; Xint; Xptr] Xint cc_default))
  [tint; tint; tint; tptr tint] tint cc_default.
Definition namespace_duplicate_definition : Clight.fundef := External
  (EF_external "entry_duplicate_above" (mksignature [Xint; Xint] Xint cc_default))
  [tint; tint] tint cc_default.
Definition namespace_mask_definition : Clight.fundef := External
  (EF_external "entry_signal_mask" (mksignature [Xlong] Xlong cc_default))
  [tulong] tlong cc_default.
Definition namespace_default_definition : Clight.fundef := External
  (EF_external "entry_signal_default" (mksignature [Xint] Xlong cc_default))
  [tint] tlong cc_default.
Definition namespace_fork_definition : Clight.fundef := External
  (EF_external "fork" (mksignature [] Xint cc_default)) [] tint cc_default.

Definition namespace_pair_owned before output offset :=
  Ptrofs.unsigned offset + 8 <= Ptrofs.modulus /\
  (Ptrofs.unsigned offset mod 4 = 0) /\
  Mem.range_perm before output (Ptrofs.unsigned offset)
    (Ptrofs.unsigned offset + 8) Cur Writable.

Definition namespace_pair_partial cell output offset before after :=
  Mem.unchanged_on (entry_outside cell output (Ptrofs.unsigned offset) 8) before after /\
  forall object position kind permission,
    Mem.perm after object position kind permission <-> Mem.perm before object position kind permission.

Inductive namespace_pair_effect cell output offset : mem -> int -> int -> int -> mem -> Prop :=
| namespace_pair_failed : forall before returned first second after,
    returned <> Int.zero -> entry_errno_partial cell before after ->
    namespace_pair_effect cell output offset before returned first second after
| namespace_pair_succeeded : forall before first second middle written after,
    Mem.store Mint32 before output (Ptrofs.unsigned offset) (Vint first) = Some middle ->
    Mem.store Mint32 middle output (Ptrofs.unsigned offset + 4) (Vint second) = Some written ->
    entry_errno_partial cell written after ->
    namespace_pair_effect cell output offset before Int.zero first second after.

Inductive namespace_ready : Clight.state -> Prop :=
| namespace_pair_ready : forall before domain kind protocol output offset k,
    namespace_pair_owned before output offset ->
    namespace_ready (Callstate namespace_pair_definition
      [Vint domain; Vint kind; Vint protocol; Vptr output offset] k before)
| namespace_duplicate_ready : forall before descriptor minimum k,
    namespace_ready (Callstate namespace_duplicate_definition [Vint descriptor;Vint minimum] k before)
| namespace_mask_ready : forall before mask k,
    namespace_ready (Callstate namespace_mask_definition [Vlong mask] k before)
| namespace_default_ready : forall before signal k,
    namespace_ready (Callstate namespace_default_definition [Vint signal] k before)
| namespace_fork_ready : forall before k,
    namespace_ready (Callstate namespace_fork_definition [] k before).

Inductive namespace_event :=
| namespace_process (event : process_event)
| namespace_paired (domain kind protocol : int) (output : block) (offset : Ptrofs.int)
    (returned first second : int)
| namespace_duplicated (descriptor minimum returned : int)
| namespace_masked (mask returned : int64)
| namespace_defaulted (signal : int) (returned : int64)
| namespace_forked (returned : int)
| namespace_pair_lost (domain kind protocol : int) (output : block) (offset : Ptrofs.int)
| namespace_duplicate_lost (descriptor minimum : int)
| namespace_mask_lost (mask : int64)
| namespace_default_lost (signal : int)
| namespace_fork_lost
| namespace_waiting.

Inductive namespace_step ge cell : machine -> namespace_event -> machine -> Prop :=
| namespace_process_step : forall before event after,
    process_step ge cell before event after ->
    namespace_step ge cell before (namespace_process event) after
| namespace_pair_step : forall before domain kind protocol output offset k returned first second after,
    namespace_pair_owned before output offset ->
    namespace_pair_effect cell output offset before returned first second after ->
    entry_errno_ready cell after ->
    namespace_step ge cell
      (live (Callstate namespace_pair_definition
        [Vint domain;Vint kind;Vint protocol;Vptr output offset] k before))
      (namespace_paired domain kind protocol output offset returned first second)
      (live (Returnstate (Vint returned) k after))
| namespace_duplicate_step : forall before descriptor minimum k returned after,
    entry_errno_partial cell before after -> entry_errno_ready cell after ->
    namespace_step ge cell
      (live (Callstate namespace_duplicate_definition [Vint descriptor;Vint minimum] k before))
      (namespace_duplicated descriptor minimum returned)
      (live (Returnstate (Vint returned) k after))
| namespace_mask_step : forall before mask k returned after,
    entry_errno_partial cell before after -> entry_errno_ready cell after ->
    namespace_step ge cell (live (Callstate namespace_mask_definition [Vlong mask] k before))
      (namespace_masked mask returned) (live (Returnstate (Vlong returned) k after))
| namespace_fork_step : forall before k returned after,
    entry_errno_partial cell before after -> entry_errno_ready cell after ->
    namespace_step ge cell (live (Callstate namespace_fork_definition [] k before))
      (namespace_forked returned) (live (Returnstate (Vint returned) k after))
| namespace_default_step : forall before signal k returned after,
    entry_errno_partial cell before after -> entry_errno_ready cell after ->
    namespace_step ge cell (live (Callstate namespace_default_definition [Vint signal] k before))
      (namespace_defaulted signal returned) (live (Returnstate (Vlong returned) k after))
| namespace_pair_loss : forall before domain kind protocol output offset k after,
    namespace_pair_owned before output offset ->
    namespace_pair_partial cell output offset before after ->
    namespace_step ge cell
      (live (Callstate namespace_pair_definition
        [Vint domain;Vint kind;Vint protocol;Vptr output offset] k before))
      (namespace_pair_lost domain kind protocol output offset) (dead after)
| namespace_duplicate_loss : forall before descriptor minimum k after,
    entry_errno_partial cell before after ->
    namespace_step ge cell
      (live (Callstate namespace_duplicate_definition [Vint descriptor;Vint minimum] k before))
      (namespace_duplicate_lost descriptor minimum) (dead after)
| namespace_mask_loss : forall before mask k after,
    entry_errno_partial cell before after ->
    namespace_step ge cell (live (Callstate namespace_mask_definition [Vlong mask] k before))
      (namespace_mask_lost mask) (dead after)
| namespace_fork_loss : forall before k after,
    entry_errno_partial cell before after ->
    namespace_step ge cell (live (Callstate namespace_fork_definition [] k before))
      namespace_fork_lost (dead after)
| namespace_default_loss : forall before signal k after,
    entry_errno_partial cell before after ->
    namespace_step ge cell (live (Callstate namespace_default_definition [Vint signal] k before))
      (namespace_default_lost signal) (dead after)
| namespace_wait_step : forall state,
    namespace_ready state -> namespace_step ge cell (live state) namespace_waiting (live state).

Inductive namespace_steps ge cell : machine -> list namespace_event -> machine -> Prop :=
| namespace_steps_nil : forall state, namespace_steps ge cell state [] state
| namespace_steps_cons : forall before event middle rest after,
    namespace_step ge cell before event middle -> namespace_steps ge cell middle rest after ->
    namespace_steps ge cell before (event::rest) after.

Lemma namespace_ready_external state : namespace_ready state -> ~internal_state state.
Proof. intro READY; inversion READY; cbn; tauto. Qed.

Theorem namespace_internal_step_exact ge cell state event after :
  internal_state state -> namespace_step ge cell (live state) event after ->
  exists original, event = namespace_process (process_entry (entry_library (original_event original))) /\
    Machine.step ge cell (live state) original after.
Proof.
  intros INTERNAL STEP; inversion STEP; subst; cbn in INTERNAL; try contradiction.
  - destruct (process_internal_step_exact _ _ _ _ _ INTERNAL H) as [original [EVENT REAL]].
    subst; eauto.
  - exfalso; eapply namespace_ready_external; eassumption.
Qed.

Theorem namespace_store_edge_cases ge cell state next event after :
  store_edge ge state next -> namespace_step ge cell (live state) event after ->
  (event = namespace_process (process_entry (entry_library (original_event (source_step E0)))) /\
    after = live next) \/
  (event = namespace_process (process_entry (entry_library (original_event loss_step))) /\
    after = dead (memory_of state)).
Proof.
  intros EDGE STEP.
  destruct (namespace_internal_step_exact _ _ _ _ _ (proj1 EDGE) STEP)
    as [original [EVENT REAL]]; subst.
  destruct (store_edge_cases _ _ _ _ _ _ EDGE REAL) as [[EVENT AFTER]|[EVENT AFTER]]; subst; auto.
Qed.

Theorem namespace_loss_everywhere ge cell state :
  namespace_step ge cell (live state)
    (namespace_process (process_entry (entry_library (original_event loss_step))))
    (dead (memory_of state)).
Proof. constructor; apply process_loss_everywhere. Qed.

Theorem namespace_dead_cannot_resume ge cell memory event after :
  ~namespace_step ge cell (dead memory) event after.
Proof.
  intro STEP; inversion STEP; subst; eapply process_dead_cannot_resume; eassumption.
Qed.

Theorem namespace_dead_steps ge cell memory events after :
  namespace_steps ge cell (dead memory) events after -> events = [] /\ after = dead memory.
Proof.
  intro RUN; inversion RUN; subst; auto.
  exfalso; eapply namespace_dead_cannot_resume; eassumption.
Qed.

Theorem namespace_process_steps_preserved ge cell before events after :
  process_steps ge cell before events after ->
  namespace_steps ge cell before (map namespace_process events) after.
Proof.
  intro RUN; induction RUN; cbn; [constructor|].
  econstructor; [constructor; exact H|exact IHRUN].
Qed.

Theorem namespace_process_projection ge cell state event after :
  ~namespace_ready state -> namespace_step ge cell (live state) event after ->
  exists original, event = namespace_process original /\ process_step ge cell (live state) original after.
Proof.
  intros OUTSIDE STEP; inversion STEP; subst; eauto;
    exfalso; apply OUTSIDE;
    eauto using namespace_pair_ready, namespace_duplicate_ready,
      namespace_mask_ready, namespace_default_ready, namespace_fork_ready.
Qed.
