(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Local ownership supplies real stores and survives each primitive's exact frame. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata.
Require Import Machine ErrorNumber Library ProcessEffects.
From EntryNative Require Import NativeHandoffMachine NativeHandoffInput.
From EntryNamespace Require Import NamespaceMachine NamespaceBorrow.
Import ListNotations.
Open Scope Z_scope.

Record ChildStorage := {
  storage_pair : block;
  storage_peer : block;
  storage_pid : block
}.

Definition child_storage cell objects m :=
  entry_errno_ready cell m /\
  Mem.range_perm m (storage_pair objects) 0 8 Cur Freeable /\
  Mem.range_perm m (storage_peer objects) 0 4 Cur Freeable /\
  Mem.range_perm m (storage_pid objects) 0 4 Cur Freeable.

Definition child_storage_separate cell objects :=
  storage_pair objects <> tls_block cell /\ storage_peer objects <> tls_block cell /\
  storage_pid objects <> tls_block cell /\ storage_peer objects <> storage_pair objects /\
  storage_pid objects <> storage_pair objects /\ storage_peer objects <> storage_pid objects.

Theorem child_storage_permissions cell objects before after :
  child_storage cell objects before -> entry_errno_ready cell after ->
  (forall object position kind permission,
    Mem.perm before object position kind permission -> Mem.perm after object position kind permission) ->
  child_storage cell objects after.
Proof.
  intros [ERRNO [PAIR [PEER PID]]] READY PERMS.
  split; [exact READY|]. split; [|split]; intros position RANGE; apply PERMS;
    [apply PAIR|apply PEER|apply PID]; exact RANGE.
Qed.

Theorem child_storage_partial cell objects before after :
  child_storage cell objects before -> entry_errno_partial cell before after ->
  entry_errno_ready cell after -> child_storage cell objects after.
Proof.
  intros OWN FRAME READY; eapply child_storage_permissions; [exact OWN|exact READY|].
  intros object position kind permission PERM.
  apply (proj2 (entry_errno_partial_permissions _ _ _ FRAME object position kind permission)); exact PERM.
Qed.

Theorem child_storage_close cell objects before after reply :
  child_storage cell objects before -> close_effect cell before reply after ->
  entry_errno_ready cell after -> child_storage cell objects after.
Proof.
  intros OWN CLOSE READY; eapply child_storage_permissions; [exact OWN|exact READY|].
  intros object position kind permission PERM.
  apply (proj2 (close_preserves_permissions _ _ _ _ CLOSE object position kind permission)); exact PERM.
Qed.

Lemma namespace_errno_ready_close cell before after reply :
  entry_errno_ready cell before -> close_effect cell before reply after -> entry_errno_ready cell after.
Proof.
  intros [error [LOW [HIGH [ACCESS LOAD]]]] [TLS UPDATE]; inversion UPDATE; subst.
  - exists error; split; [exact LOW|]. split; [exact HIGH|]. split; assumption.
  - exists value; split; [exact LOW|]. split; [exact HIGH|]. split.
    + destruct ACCESS as [PERMS ALIGN]; split; [|exact ALIGN].
      intros position RANGE; eapply Mem.perm_store_1; [eassumption|apply PERMS; exact RANGE].
    + erewrite Mem.load_store_same by eassumption; reflexivity.
Qed.

Theorem child_pair_is_writable cell objects m : child_storage cell objects m ->
  namespace_pair_owned m (storage_pair objects) Ptrofs.zero.
Proof.
  intros [ERRNO [PAIR REST]]; split; [vm_compute; discriminate|].
  split; [reflexivity|]; change (Mem.range_perm m (storage_pair objects) 0 8 Cur Writable).
  intros position RANGE; eapply Mem.perm_implies; [apply PAIR; exact RANGE|constructor].
Qed.

Lemma child_integer_cell_writable m object : Mem.range_perm m object 0 4 Cur Freeable ->
  Mem.valid_access m Mint32 object 0 Writable.
Proof.
  intro OWN; split.
  - intros position RANGE; eapply Mem.perm_implies; [apply OWN; exact RANGE|constructor].
  - exists 0; reflexivity.
Qed.

Theorem child_peer_store_exists cell objects before first : child_storage cell objects before ->
  exists after, Mem.store Mint32 before (storage_peer objects) 0 (Vint first) = Some after.
Proof.
  intros [ERRNO [PAIR [PEER PID]]].
  destruct (Mem.valid_access_store _ _ _ _ (Vint first) (child_integer_cell_writable _ _ PEER))
    as [after STORE]; eauto.
Qed.

Theorem child_pid_store_exists cell objects before pid : child_storage cell objects before ->
  exists after, Mem.store Mint32 before (storage_pid objects) 0 (Vint pid) = Some after.
Proof.
  intros [ERRNO [PAIR [PEER PID]]].
  destruct (Mem.valid_access_store _ _ _ _ (Vint pid) (child_integer_cell_writable _ _ PID))
    as [after STORE]; eauto.
Qed.

Lemma namespace_partial_preserves_load cell before after chunk object offset value :
  entry_errno_partial cell before after -> object <> tls_block cell ->
  Mem.load chunk before object offset = Some value -> Mem.load chunk after object offset = Some value.
Proof.
  intros FRAME DIFFERENT LOAD; eapply Mem.load_unchanged_on;
    [exact (entry_errno_partial_frame _ _ _ FRAME)| |exact LOAD].
  intros position RANGE; left; exact DIFFERENT.
Qed.

Theorem namespace_pair_returned_cells cell before after object offset first second :
  object <> tls_block cell ->
  namespace_pair_effect cell object offset before Int.zero first second after ->
  Mem.load Mint32 after object (Ptrofs.unsigned offset) = Some (Vint first) /\
  Mem.load Mint32 after object (Ptrofs.unsigned offset+4) = Some (Vint second).
Proof.
  intros TLS PAIR; inversion PAIR; subst; [contradiction|].
  split; eapply namespace_partial_preserves_load; [eassumption|exact TLS| |eassumption|exact TLS|].
  - erewrite Mem.load_store_other by (eassumption || (right; left; cbn; lia)).
    erewrite Mem.load_store_same by eassumption; reflexivity.
  - erewrite Mem.load_store_same by eassumption; reflexivity.
Qed.

Theorem namespace_pair_permissions cell before after object offset returned first second :
  namespace_pair_effect cell object offset before returned first second after ->
  forall target position kind permission,
    Mem.perm before target position kind permission -> Mem.perm after target position kind permission.
Proof.
  intro PAIR; inversion PAIR; subst; intros target position kind permission PERM.
  all: match goal with FRAME : entry_errno_partial _ _ _ |- _ =>
    apply (proj2 (entry_errno_partial_permissions _ _ _ FRAME target position kind permission)) end.
  all: eauto using Mem.perm_store_1.
Qed.

Theorem namespace_store_storage cell objects input before after target offset chunk value :
  child_storage cell objects before -> child_storage_separate cell objects ->
  handoff_borrowed_input cell before input -> ~In target (handoff_borrowed_blocks input) ->
  target <> tls_block cell -> Mem.store chunk before target offset value = Some after ->
  child_storage cell objects after /\ handoff_borrowed_input cell after input.
Proof.
  intros OWN SEPARATE INPUT PRIVATE TLS STORE.
  pose proof (namespace_store_preserves_borrows _ _ _ _ _ _ _ _ INPUT PRIVATE TLS STORE) as AFTER.
  split; [|exact AFTER].
  eapply child_storage_permissions; [exact OWN|exact (handoff_borrowed_errno _ _ _ AFTER)|].
  intros; eapply Mem.perm_store_1; eassumption.
Qed.

Theorem namespace_free_preserves_load before after object low high chunk other offset value :
  Mem.free before object low high = Some after -> other <> object ->
  Mem.load chunk before other offset = Some value -> Mem.load chunk after other offset = Some value.
Proof.
  intros FREE DIFFERENT LOAD; eapply Mem.load_unchanged_on with (P:=fun target _=>target<>object);
    [eapply Mem.free_unchanged_on; [exact FREE|]| |exact LOAD].
  - intros position RANGE NEQ; apply NEQ; reflexivity.
  - intros position RANGE; exact DIFFERENT.
Qed.
