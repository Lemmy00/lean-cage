(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.effects: Classify every return, wait and loss at local namespace primitives. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Clight.
Require Import IO Machine LibraryMachine ProcessEffects.
From EntryNative Require Import NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine.
From EntryNamespace Require Import NamespaceMachine.
Import ListNotations.
Open Scope Z_scope.

Inductive NamespacePrimitive := pair_primitive | duplicate_primitive | mask_primitive | default_primitive | fork_primitive.
Definition namespace_primitive primitive :=
  match primitive with
  | pair_primitive => namespace_pair_definition
  | duplicate_primitive => namespace_duplicate_definition
  | mask_primitive => namespace_mask_definition
  | default_primitive => namespace_default_definition
  | fork_primitive => namespace_fork_definition
  end.

Lemma namespace_primitive_process_only_loss ge cell primitive arguments k before event target :
  process_step ge cell (live (Callstate (namespace_primitive primitive) arguments k before)) event target ->
  event = process_entry (entry_library (original_event loss_step)) /\ target = dead before.
Proof.
  destruct primitive; intros STEP; inversion STEP; subst; try discriminate.
  all: match goal with BASE : entry_handoff_step _ _ _ _ _ |- _ =>
    inversion BASE; subst; clear BASE; try discriminate end.
  all: match goal with BASE : library_step _ _ _ _ _ |- _ =>
    inversion BASE; subst; clear BASE; try discriminate end.
  all: try match goal with READY : library_ready _ _ |- _ => inversion READY end.
  all: match goal with BASE : Machine.step _ _ _ _ _ |- _ =>
    inversion BASE; subst; cbn in *; try contradiction; auto end.
  all: match goal with BOUNDARY : boundary _ _ _ |- _ =>
    inversion BOUNDARY; subst; destruct (operation q); discriminate end.
Qed.

Theorem namespace_pair_cases ge cell before domain kind protocol output offset k event target :
  namespace_step ge cell
    (live (Callstate namespace_pair_definition [Vint domain;Vint kind;Vint protocol;Vptr output offset] k before))
    event target ->
  (exists returned first second after,
    namespace_pair_owned before output offset /\
    namespace_pair_effect cell output offset before returned first second after /\
    entry_errno_ready cell after /\
    event = namespace_paired domain kind protocol output offset returned first second /\
    target = live (Returnstate (Vint returned) k after)) \/
  (event = namespace_waiting /\ target = live
    (Callstate namespace_pair_definition [Vint domain;Vint kind;Vint protocol;Vptr output offset] k before)) \/
  (exists after, namespace_pair_partial cell output offset before after /\
    event = namespace_pair_lost domain kind protocol output offset /\ target = dead after) \/
  (event = namespace_process (process_entry (entry_library (original_event loss_step))) /\ target = dead before).
Proof.
  intro STEP; inversion STEP; subst; try discriminate.
  - destruct (namespace_primitive_process_only_loss ge cell pair_primitive _ _ _ _ _ H) as [EVENT TARGET];
      subst; right; right; right; auto.
  - left; do 4 eexists; split; [eassumption|]. split; [eassumption|].
    split; [eassumption|]. split; reflexivity.
  - right; right; left; eexists; split; [eassumption|]. split; reflexivity.
  - right; left; auto.
Qed.

Theorem namespace_duplicate_cases ge cell before descriptor minimum k event target :
  namespace_step ge cell
    (live (Callstate namespace_duplicate_definition [Vint descriptor;Vint minimum] k before)) event target ->
  (exists returned after, entry_errno_partial cell before after /\ entry_errno_ready cell after /\
    event = namespace_duplicated descriptor minimum returned /\ target = live (Returnstate (Vint returned) k after)) \/
  (event = namespace_waiting /\ target = live
    (Callstate namespace_duplicate_definition [Vint descriptor;Vint minimum] k before)) \/
  (exists after, entry_errno_partial cell before after /\
    event = namespace_duplicate_lost descriptor minimum /\ target = dead after) \/
  (event = namespace_process (process_entry (entry_library (original_event loss_step))) /\ target = dead before).
Proof.
  intro STEP; inversion STEP; subst; try discriminate.
  - destruct (namespace_primitive_process_only_loss ge cell duplicate_primitive _ _ _ _ _ H) as [EVENT TARGET];
      subst; right; right; right; auto.
  - left; do 2 eexists; split; [eassumption|]. split; [eassumption|]. split; reflexivity.
  - right; right; left; eexists; split; [eassumption|]. split; reflexivity.
  - right; left; auto.
Qed.

Theorem namespace_mask_cases ge cell before mask k event target :
  namespace_step ge cell (live (Callstate namespace_mask_definition [Vlong mask] k before)) event target ->
  (exists returned after, entry_errno_partial cell before after /\ entry_errno_ready cell after /\
    event = namespace_masked mask returned /\ target = live (Returnstate (Vlong returned) k after)) \/
  (event = namespace_waiting /\ target = live (Callstate namespace_mask_definition [Vlong mask] k before)) \/
  (exists after, entry_errno_partial cell before after /\ event = namespace_mask_lost mask /\ target = dead after) \/
  (event = namespace_process (process_entry (entry_library (original_event loss_step))) /\ target = dead before).
Proof.
  intro STEP; inversion STEP; subst; try discriminate.
  - destruct (namespace_primitive_process_only_loss ge cell mask_primitive _ _ _ _ _ H) as [EVENT TARGET];
      subst; right; right; right; auto.
  - left; do 2 eexists; split; [eassumption|]. split; [eassumption|]. split; reflexivity.
  - right; right; left; eexists; split; [eassumption|]. split; reflexivity.
  - right; left; auto.
Qed.

Theorem namespace_default_cases ge cell before signal k event target :
  namespace_step ge cell (live (Callstate namespace_default_definition [Vint signal] k before)) event target ->
  (exists returned after, entry_errno_partial cell before after /\ entry_errno_ready cell after /\
    event = namespace_defaulted signal returned /\ target = live (Returnstate (Vlong returned) k after)) \/
  (event = namespace_waiting /\ target = live (Callstate namespace_default_definition [Vint signal] k before)) \/
  (exists after, entry_errno_partial cell before after /\ event = namespace_default_lost signal /\ target = dead after) \/
  (event = namespace_process (process_entry (entry_library (original_event loss_step))) /\ target = dead before).
Proof.
  intro STEP; inversion STEP; subst; try discriminate.
  - destruct (namespace_primitive_process_only_loss ge cell default_primitive _ _ _ _ _ H) as [EVENT TARGET];
      subst; right; right; right; auto.
  - left; do 2 eexists; split; [eassumption|]. split; [eassumption|]. split; reflexivity.
  - right; right; left; eexists; split; [eassumption|]. split; reflexivity.
  - right; left; auto.
Qed.


Theorem namespace_fork_cases ge cell before k event target :
  namespace_step ge cell (live (Callstate namespace_fork_definition [] k before)) event target ->
  (exists returned after, entry_errno_partial cell before after /\ entry_errno_ready cell after /\
    event = namespace_forked returned /\ target = live (Returnstate (Vint returned) k after)) \/
  (event = namespace_waiting /\ target = live (Callstate namespace_fork_definition [] k before)) \/
  (exists after, entry_errno_partial cell before after /\ event = namespace_fork_lost /\ target = dead after) \/
  (event = namespace_process (process_entry (entry_library (original_event loss_step))) /\ target = dead before).
Proof.
  intro STEP; inversion STEP; subst; try discriminate.
  - destruct (namespace_primitive_process_only_loss ge cell fork_primitive _ _ _ _ _ H) as [EVENT TARGET];
      subst; right; right; right; auto.
  - left; do 2 eexists; split; [eassumption|]. split; [eassumption|]. split; reflexivity.
  - right; right; left; eexists; split; [eassumption|]. split; reflexivity.
  - right; left; auto.
Qed.
