(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.effects: Actual namespace source and primitive transitions retain the real TLS allocation. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Values Memory Events Clight.
Require Import IO Machine LibraryMachine ProcessEffects.
From EntryNative Require Import NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine ProcessMemory.
From EntryNamespace Require Import NamespaceMachine.
Import ListNotations.
Open Scope Z_scope.

Lemma namespace_errno_ready_valid cell memory:
  entry_errno_ready cell memory ->Mem.valid_block memory(tls_block cell).
Proof.
  intros[error[LOW[HIGH[ACCESS LOAD]]]].
  eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;[exact ACCESS|constructor].
Qed.

Theorem namespace_step_tls_valid ge cell before event after:
  namespace_step ge cell before event after ->
  Mem.valid_block(machine_memory before)(tls_block cell) ->
  Mem.valid_block(machine_memory after)(tls_block cell).
Proof.
  intros STEP VALID;inversion STEP;subst;cbn[machine_memory]in *;auto.
  all:try solve[eapply process_step_tls_valid;eassumption].
  all:try solve[match goal with READY:entry_errno_ready _ _|-_=>
    exact(namespace_errno_ready_valid _ _ READY)end].
  all:try solve[match goal with PARTIAL:entry_errno_partial _ _ _|-_=>
    eapply Mem.valid_block_unchanged_on;[exact(entry_errno_partial_frame _ _ _ PARTIAL)|exact VALID]end].
  destruct H0 as[FRAME PERMISSIONS];eapply Mem.valid_block_unchanged_on;eassumption.
Qed.

Theorem namespace_steps_tls_valid ge cell before events after:
  namespace_steps ge cell before events after ->
  Mem.valid_block(machine_memory before)(tls_block cell) ->
  Mem.valid_block(machine_memory after)(tls_block cell).
Proof. intros RUN;induction RUN;intros VALID;[exact VALID|apply IHRUN;eapply namespace_step_tls_valid;eassumption]. Qed.
