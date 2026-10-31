(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-receiver.memory: Every close result retains private error bytes and constructor inputs. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata Clight.
Require Import IO Machine ProcessEffects WriteEffects ResultLayout ResultOwnership SenderReportMemory
  ReceiverSource ReceiverAllocation ReceiverPreparation ReceiverReadMemory
  ReceiverMemory ReceiverInput.
Import ListNotations.
Open Scope Z_scope.
Lemma close_tls_history : forall cell m reply after,
  close_effect cell m reply after -> tls_history cell m after.
Proof.
  intros cell m reply after [READY UPDATE];inversion UPDATE;subst;[constructor|].
  econstructor;[eassumption|constructor].
Qed.
Theorem receiver_live_close : forall cell base b output ofs fd before reply after,
  tls_ready cell base -> receiver_live_memory cell base b output ofs fd before ->
  close_effect cell before reply after -> receiver_live_memory cell base b output ofs fd after.
Proof.
  intros cell base b output ofs fd before reply after TLS [OLD[SLOTS[DEST FD]]] EFFECT.
  assert(PERMS : old_permissions before after).
  { intros object pos pk permission PERM;apply(close_preserves_permissions _ _ _ _ EFFECT);exact PERM. }
  split;[eapply history_sender_preserved;[exact OLD|eapply close_tls_history;exact EFFECT]|].
  split;[eapply receiver_slots_permissions;[exact SLOTS|exact PERMS]|].
  split;[eapply receiver_destination_permissions;[exact DEST|exact PERMS]|].
  eapply Mem.load_unchanged_on;[eapply close_preserves_outside_tls;exact EFFECT| |exact FD].
  intros pos RANGE;left;eapply fresh_tls_separate;[exact TLS|].
  exact(proj1(receiver_slot base b before(rb_pipe b)4 SLOTS ltac:(unfold receiver_objects;cbn;tauto))).
Qed.
Theorem receiver_buffer_close : forall cell b before reply after bytes,
  receiver_buffer cell b before bytes -> close_effect cell before reply after ->
  receiver_buffer cell b after bytes.
Proof. intros;eapply receiver_buffer_tls;[exact H|eapply close_tls_history;exact H0]. Qed.
