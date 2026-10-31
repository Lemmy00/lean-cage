(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-library.process: Local close/TLS effects without a cleanup receipt. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory.
Require Import IO Machine ErrorNumber WriteBytes.
Import ListNotations.
Open Scope Z_scope.

Definition tls_ready cell m :=
  0 <= tls_offset cell /\ tls_offset cell + 4 <= Ptrofs.modulus /\
  Mem.valid_access m Mint32 (tls_block cell) (tls_offset cell) Writable.
Inductive tls_update cell : mem -> option int -> mem -> Prop :=
| tls_unchanged : forall m, tls_update cell m None m
| tls_written : forall m value after,
    Mem.store Mint32 m (tls_block cell) (tls_offset cell) (Vint value) = Some after ->
    tls_update cell m (Some value) after.
Inductive close_reply := close_ok (error : option int) | close_error (error : int).
Definition close_value reply := match reply with close_ok _ => Int.zero | close_error _ => Int.mone end.
Definition close_errno reply := match reply with close_ok error => error | close_error error => Some error end.
Definition close_effect cell m reply after := tls_ready cell m /\ tls_update cell m (close_errno reply) after.

Theorem tls_update_exists : forall cell m value,
  tls_ready cell m -> exists after, tls_update cell m value after.
Proof.
  intros cell m value [_ [_ ACCESS]]. destruct value as [value|].
  - destruct (Mem.valid_access_store _ _ _ _ (Vint value) ACCESS) as [after STORE].
    exists after; constructor; assumption.
  - exists m; constructor.
Qed.

Theorem close_progress : forall cell m reply,
  tls_ready cell m -> exists after, close_effect cell m reply after.
Proof.
  intros cell m reply READY. destruct (tls_update_exists _ _ (close_errno reply) READY)
    as [after UPDATE]. exists after; split; assumption.
Qed.

Theorem close_return_range : forall reply,
  close_value reply = Int.zero \/ close_value reply = Int.mone.
Proof. destruct reply; cbn; auto. Qed.

Theorem close_error_stores_errno : forall cell m error after,
  close_effect cell m (close_error error) after ->
  Mem.load Mint32 after (tls_block cell) (tls_offset cell) = Some (Vint error).
Proof.
  intros cell m error after [_ UPDATE]; inversion UPDATE; subst.
  erewrite Mem.load_store_same by eassumption; reflexivity.
Qed.

Theorem tls_update_deterministic : forall cell m error a b,
  tls_update cell m error a -> tls_update cell m error b -> a = b.
Proof. intros cell m error a b A B; inversion A; inversion B; subst; congruence. Qed.

Theorem close_effect_deterministic : forall cell m reply a b,
  close_effect cell m reply a -> close_effect cell m reply b -> a = b.
Proof. intros cell m reply a b [_ A] [_ B]; eapply tls_update_deterministic; eassumption. Qed.

Theorem close_preserves_permissions : forall cell m reply after,
  close_effect cell m reply after ->
  forall b pos kind perm, Mem.perm after b pos kind perm <-> Mem.perm m b pos kind perm.
Proof.
  intros cell m reply after [_ UPDATE]; inversion UPDATE; subst; intros; [tauto|].
  split; eauto using Mem.perm_store_1, Mem.perm_store_2.
Qed.

Theorem close_preserves_outside_tls : forall cell m reply after,
  close_effect cell m reply after ->
  Mem.unchanged_on (outside_bytes (tls_block cell) (tls_offset cell) 4) m after.
Proof.
  intros cell m reply after [_ UPDATE]; inversion UPDATE; subst; [apply Mem.unchanged_on_refl|].
  eapply Mem.store_unchanged_on; [eassumption|].
  unfold outside_bytes; cbn; intros pos BOUND [NE|[LOW|HIGH]]; lia.
Qed.

Theorem allocated_close_effects : forall (base : mem) reply,
  exists cell m after, tls_ready cell m /\ close_effect cell m reply after.
Proof.
  intros base reply. destruct (allocated_errno base Int.zero) as [allocated [b [m [_ [_ OWN]]]]].
  set (cell := {|tls_block := b; tls_offset := 0|}) in *.
  assert (READY : tls_ready cell m) by (destruct OWN as [A [B [C D]]]; unfold tls_ready; auto).
  destruct (close_progress _ _ reply READY) as [after EFFECT]. eauto.
Qed.
