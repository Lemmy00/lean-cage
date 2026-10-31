(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-receiver.reads: Exact initialized read prefixes and independent writable capacity. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata.
Require Import IO Machine WriteAll WriteBytes Library ProcessEffects WriteEffects
  SenderReportMemory ReceiverSource.
Import ListNotations.
Open Scope Z_scope.

Definition receiver_buffer cell b m bytes :=
  (length bytes<=9)%nat /\ tls_ready cell m /\ rb_bytes b<>tls_block cell /\
  Mem.range_perm m (rb_bytes b) 0 9 Cur Freeable /\
  Mem.loadbytes m (rb_bytes b) 0 (Z.of_nat(length bytes))=Some(map Byte bytes).

Theorem receiver_read_owned : forall cell b fd m bytes,
  receiver_buffer cell b m bytes -> (length bytes<9)%nat ->
  owned (receiver_request b cell fd (Z.of_nat(length bytes))) m.
Proof.
  intros cell b fd m bytes [LEN [[LOW [HIGH TLS]] [NE [PERMS LOAD]]]] SHORT.
  unfold owned,receiver_request;cbn [operation buffer_block buffer_offset requested errno_block errno_offset].
  split;[lia|]. split;[change Ptrofs.modulus with 18446744073709551616;lia|].
  split;[change Ptrofs.modulus with 18446744073709551616;lia|].
  split;[exact LOW|]. split;[exact HIGH|]. split;[exact TLS|].
  split;[left;exact NE|]. intros pos RANGE;eapply Mem.perm_implies;[apply PERMS;lia|constructor].
Qed.

Lemma receiver_request_cell : forall b cell fd used,
  cell_of (receiver_request b cell fd used)=cell.
Proof. destruct cell;reflexivity. Qed.

Theorem receiver_buffer_tls : forall cell b before after bytes,
  receiver_buffer cell b before bytes -> tls_history cell before after ->
  receiver_buffer cell b after bytes.
Proof.
  intros cell b before after bytes [LEN [TLS [NE [PERMS LOAD]]]] HISTORY.
  split;[exact LEN|]. split;[eapply tls_history_ready;eassumption|]. split;[exact NE|]. split.
  - intros pos RANGE;apply (tls_history_permissions _ _ _ HISTORY);apply PERMS;exact RANGE.
  - eapply Mem.loadbytes_unchanged_on;[eapply tls_history_outside;exact HISTORY|intros;left;exact NE|exact LOAD].
Qed.

Lemma storebytes_tls_ready : forall cell m buffer ofs values after,
  tls_ready cell m -> Mem.storebytes m buffer ofs values=Some after -> tls_ready cell after.
Proof.
  intros cell m buffer ofs values after [LOW [HIGH [PERMS ALIGN]]] STORE.
  split;[exact LOW|]. split;[exact HIGH|]. split;[|exact ALIGN].
  intros pos RANGE;eapply Mem.perm_storebytes_1;[exact STORE|apply PERMS;exact RANGE].
Qed.

Theorem receiver_buffer_transfer : forall cell b fd before after prefix bytes error,
  receiver_buffer cell b before prefix ->
  io_return (receiver_request b cell fd (Z.of_nat(length prefix))) before (transfer bytes error) after ->
  receiver_buffer cell b after (prefix++bytes).
Proof.
  intros cell b fd before after prefix bytes error BUFFER EFFECT.
  pose proof BUFFER as [LEN [TLS [NE [PERMS LOAD]]]].
  inversion EFFECT;subst;try discriminate.
  match goal with COPY : Mem.storebytes _ _ _ _=Some ?copied,
    ERR : errno_change _ ?copied _ _ |- _=>
    assert (COPIED : receiver_buffer cell b copied (prefix++bytes));
    [|eapply receiver_buffer_tls;[exact COPIED|pose proof (errno_history _ _ _ _ ERR) as HISTORY;
        rewrite receiver_request_cell in HISTORY;exact HISTORY]] end.
  assert (SIZE : 0<Z.of_nat(length bytes)<=9-Z.of_nat(length prefix)).
  { match goal with BOUND : 0<Z.of_nat(length bytes)<=_ |- _=>exact BOUND end. }
  split;[rewrite app_length;lia|].
  split;[eapply storebytes_tls_ready;[exact TLS|eassumption]|]. split;[exact NE|]. split.
  - intros pos RANGE;eapply Mem.perm_storebytes_1;[eassumption|apply PERMS;exact RANGE].
  - rewrite app_length,Nat2Z.inj_add,map_app;eapply Mem.loadbytes_concat;[| |lia|lia].
    + erewrite Mem.loadbytes_storebytes_other;[exact LOAD|eassumption|lia|right;left;cbn;lia].
    + rewrite Z.add_0_l.
      match goal with COPY : Mem.storebytes _ _ _ _=Some _ |- _=>
        pose proof (Mem.loadbytes_storebytes_same _ _ _ _ _ COPY) as NEW end.
      rewrite map_length in NEW;exact NEW.
Qed.

Definition receiver_reply_bytes reply := match reply with transfer bytes _=>bytes|_=>[] end.
Theorem receiver_buffer_reply : forall cell b fd before after prefix reply,
  receiver_buffer cell b before prefix ->
  io_return (receiver_request b cell fd (Z.of_nat(length prefix))) before reply after ->
  receiver_buffer cell b after (prefix++receiver_reply_bytes reply).
Proof.
  intros cell b fd before after prefix reply BUFFER EFFECT;destruct reply as [bytes error|error|error].
  - eapply receiver_buffer_transfer;eassumption.
  - cbn [receiver_reply_bytes];rewrite app_nil_r;eapply receiver_buffer_tls;[exact BUFFER|].
    inversion EFFECT;subst;match goal with ERR : errno_change _ _ _ _ |- _=>
      pose proof (errno_history _ _ _ _ ERR) as HISTORY end.
    rewrite receiver_request_cell in HISTORY;exact HISTORY.
  - cbn [receiver_reply_bytes];rewrite app_nil_r;eapply receiver_buffer_tls;[exact BUFFER|].
    inversion EFFECT;subst;match goal with ERR : errno_change _ _ _ _ |- _=>
      pose proof (errno_history _ _ _ _ ERR) as HISTORY end.
    rewrite receiver_request_cell in HISTORY;exact HISTORY.
Qed.

Theorem receiver_io_old_preserved : forall cell base b fd used before reply after,
  ~Mem.valid_block base (rb_bytes b) -> sender_preserved cell base before ->
  io_return (receiver_request b cell fd used) before reply after ->
  sender_preserved cell base after.
Proof.
  intros cell base b fd used before reply after FRESH OLD EFFECT.
  inversion EFFECT;subst;try discriminate.
  all: match goal with ERR : errno_change _ ?middle _ _ |- _=>
    eapply history_sender_preserved with (before:=middle);
    [|pose proof (errno_history _ _ _ _ ERR) as HISTORY;
      rewrite receiver_request_cell in HISTORY;exact HISTORY] end;try exact OLD.
  eapply Mem.unchanged_on_trans;[exact OLD|].
  eapply Mem.storebytes_unchanged_on;[eassumption|].
  intros pos RANGE [VALID _];contradiction.
Qed.
