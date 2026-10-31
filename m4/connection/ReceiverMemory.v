(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-receiver.memory: Receiver writes are confined to private storage, caller output and TLS. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata.
Require Import IO Machine WriteBytes ProcessEffects FreshMemory ResultLayout ResultSafety
  ResultOwnership SenderReportMemory ReceiverSource ReceiverAllocation ReceiverPreparation.
Import ListNotations.
Open Scope Z_scope.
Definition receiver_outside cell base output ofs b pos :=
  Mem.valid_block base b /\ outside_bytes(tls_block cell)(tls_offset cell)4 b pos /\
    outside_bytes output ofs 144 b pos.
Definition receiver_preserved cell base output ofs after :=
  Mem.unchanged_on(receiver_outside cell base output ofs)base after.
Lemma receiver_sender_preserved : forall cell base output ofs after,
  sender_preserved cell base after -> receiver_preserved cell base output ofs after.
Proof. intros;eapply Mem.unchanged_on_implies;[exact H|intros;unfold receiver_outside in *;tauto]. Qed.
Lemma receiver_old_preserved : forall cell base output ofs after,
  old_memory base after -> receiver_preserved cell base output ofs after.
Proof. intros;apply receiver_sender_preserved;apply old_sender_preserved;exact H. Qed.
Lemma receiver_fresh_result_preserved : forall cell base output ofs before after local,
  ~Mem.valid_block base local -> receiver_preserved cell base output ofs before ->
  result_preserved before local 0 after -> receiver_preserved cell base output ofs after.
Proof.
  intros cell base output ofs before after local FRESH PRE RESULT.
  eapply Mem.unchanged_on_trans;[exact PRE|].
  eapply Mem.unchanged_on_implies;[exact RESULT|].
  intros b pos [VALID[OTHER OUTSIDE]] VALIDBEFORE;split;[exact VALIDBEFORE|].
  left;intro EQ;subst b;contradiction.
Qed.
Lemma receiver_copy_preserved : forall cell base output ofs before after destination offset count,
  receiver_preserved cell base output ofs before ->
  Mem.unchanged_on(outside_bytes destination offset count)before after ->
  (forall b pos,receiver_outside cell base output ofs b pos -> outside_bytes destination offset count b pos) ->
  receiver_preserved cell base output ofs after.
Proof.
  intros cell base output ofs before after destination offset count PRE COPY OUTSIDE.
  eapply Mem.unchanged_on_trans;[exact PRE|].
  eapply Mem.unchanged_on_implies;[exact COPY|intros;apply OUTSIDE;assumption].
Qed.
Lemma receiver_slots_permissions : forall base b before after,
  receiver_slots_owned base b before -> old_permissions before after -> receiver_slots_owned base b after.
Proof.
  intros base b before after [DISTINCT OWN] KEEP;split;[exact DISTINCT|].
  rewrite Forall_forall in *;intros [local size] IN;destruct(OWN _ IN)as[FRESH PERMS];split;[exact FRESH|].
  intros pos RANGE;apply KEEP;apply PERMS;exact RANGE.
Qed.
Lemma receiver_destination_permissions : forall before after output ofs,
  result_destination before output ofs -> old_permissions before after -> result_destination after output ofs.
Proof.
  intros before after output ofs [LOW[HIGH[ALIGN PERMS]]] KEEP;split;[exact LOW|].
  split;[exact HIGH|]. split;[exact ALIGN|]. intros pos RANGE;apply KEEP;apply PERMS;exact RANGE.
Qed.
Lemma receiver_local_destination : forall base b m local,
  receiver_slots_owned base b m -> In(local,144)(receiver_objects b) -> result_destination m local 0.
Proof.
  intros base b m local OWN IN;destruct(receiver_slot _ _ _ _ _ OWN IN)as[FRESH PERMS].
  split;[lia|]. split;[change(144<=18446744073709551616);lia|].
  split;[exists 0;reflexivity|]. intros pos RANGE;eapply Mem.perm_implies;[apply PERMS;exact RANGE|constructor].
Qed.
Lemma receiver_copy_slots : forall base b before dst ofs values after,
  receiver_slots_owned base b before -> Mem.storebytes before dst ofs values=Some after ->
  receiver_slots_owned base b after.
Proof. intros;eapply receiver_slots_permissions;[exact H|]. intros a pos pk p PERM;eapply Mem.perm_storebytes_1;eassumption. Qed.
