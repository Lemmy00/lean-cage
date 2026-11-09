(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller.clock: A fresh timespec copy preserves every old caller object outside errno. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata Events.
Require Import IO Machine ErrorNumber ScalarMemory.
From EntryNative Require Import NativeHandoffMachine.
From EntryProcess Require Import ProcessMachine.
Import ListNotations.
Open Scope Z_scope.

Definition clock_old_location cell base object position:=Mem.valid_block base object /\
  (object<>tls_block cell \/position<tls_offset cell \/tls_offset cell+4<=position).
Definition clock_old_frame cell base after:=Mem.unchanged_on(clock_old_location cell base)base after.

Lemma clock_value_loads cell output before seconds nanos after:
  output<>tls_block cell ->
  process_clock_effect cell output Ptrofs.zero before(clock_value seconds nanos)after ->
  Mem.load Mint64 after output 0=Some(Vlong seconds) /\
  Mem.load Mint64 after output 8=Some(Vlong nanos).
Proof.
  intros SEPARATE EFFECT;inversion EFFECT;subst.
  match goal with COPY:Mem.storebytes _ _ _ _=Some _|-_=>
    pose proof(Mem.loadbytes_storebytes_same _ _ _ _ _ COPY)as BYTES end.
  assert(LENGTH:Z.of_nat(length(encode_val Mint64(Vlong seconds)++encode_val Mint64(Vlong nanos)))=16).
  { rewrite app_length,!encode_val_length;reflexivity. }
  pose proof(loadbytes_slice _ _ _ _ 0 8 BYTES ltac:(lia)ltac:(lia)ltac:(rewrite LENGTH;lia))as SECONDS_BYTES.
  change(Mem.loadbytes copied output 0 8=
    Some(firstn 8(encode_val Mint64(Vlong seconds)++encode_val Mint64(Vlong nanos))))in SECONDS_BYTES.
  rewrite firstn_app,firstn_all2 in SECONDS_BYTES by(rewrite encode_val_length;cbn;lia).
  rewrite encode_val_length in SECONDS_BYTES;cbn[size_chunk_nat]in SECONDS_BYTES.
  rewrite app_nil_r in SECONDS_BYTES.
  pose proof(loadbytes_slice _ _ _ _ 8 8 BYTES ltac:(lia)ltac:(lia)ltac:(rewrite LENGTH;lia))as NANOS_BYTES.
  rewrite skipn_app,skipn_all2 in NANOS_BYTES by(rewrite encode_val_length;cbn;lia).
  rewrite encode_val_length in NANOS_BYTES;cbn[size_chunk_nat]in NANOS_BYTES.
  rewrite firstn_all2 in NANOS_BYTES by
    (change(length(encode_val Mint64(Vlong nanos))<=8)%nat;rewrite encode_val_length;reflexivity).
  assert(SECONDS_LOAD:Mem.load Mint64 copied output 0=Some(Vlong seconds)).
  { rewrite <-(decode_encode_val_general(Vlong seconds)Mint64 Mint64).
    eapply Mem.loadbytes_load;[exact SECONDS_BYTES|exists 0;reflexivity]. }
  assert(NANOS_LOAD:Mem.load Mint64 copied output 8=Some(Vlong nanos)).
  { rewrite <-(decode_encode_val_general(Vlong nanos)Mint64 Mint64).
    eapply Mem.loadbytes_load;[exact NANOS_BYTES|exists 1;reflexivity]. }
  match goal with ERRNO:errno_change _ _ _ _|-_=>inversion ERRNO;subst end.
  - auto.
  - split;erewrite Mem.load_store_other;
      [exact SECONDS_LOAD|eassumption|left;exact SEPARATE|
       exact NANOS_LOAD|eassumption|left;exact SEPARATE].
Qed.

Lemma clock_effect_permissions cell output offset before observation after:
  process_clock_effect cell output offset before observation after ->
  forall object position kind permission,
    Mem.perm after object position kind permission<->Mem.perm before object position kind permission.
Proof.
  intro EFFECT;inversion EFFECT;subst.
  - match goal with PARTIAL:process_clock_partial _ _ _ _ _|-_=>exact(proj2 PARTIAL)end.
  - intros object position kind permission.
    match goal with ERRNO:errno_change _ _ _ _|-_=>inversion ERRNO;subst end.
    + split;eauto using Mem.perm_storebytes_1,Mem.perm_storebytes_2.
    + split;intro PERM.
      * eapply Mem.perm_storebytes_2;[eassumption|]. eapply Mem.perm_store_2;eassumption.
      * eapply Mem.perm_store_1;[eassumption|]. eapply Mem.perm_storebytes_1;eassumption.
Qed.

Lemma clock_effect_frame cell output offset before observation after:
  process_clock_effect cell output offset before observation after ->
  Mem.unchanged_on(entry_outside cell output(Ptrofs.unsigned offset)16)before after.
Proof.
  intro EFFECT;inversion EFFECT;subst.
  - match goal with PARTIAL:process_clock_partial _ _ _ _ _|-_=>exact(proj1 PARTIAL)end.
  - eapply Mem.unchanged_on_trans.
    + eapply Mem.storebytes_unchanged_on;[eassumption|].
      intros position RANGE[OUTSIDE TLS].
      rewrite app_length,!encode_val_length in RANGE;cbn in RANGE.
      destruct OUTSIDE as[DIFFERENT|[LOW|HIGH]];[congruence|lia|lia].
    + match goal with ERRNO:errno_change _ _ _ _|-_=>inversion ERRNO;subst end.
      * apply Mem.unchanged_on_refl.
      * eapply Mem.store_unchanged_on;[eassumption|].
        intros position RANGE[OUTSIDE TLS];cbn in RANGE,TLS.
        destruct TLS as[DIFFERENT|[LOW|HIGH]];[congruence|lia|lia].
Qed.

Lemma clock_copy_errno_ready cell before output offset bytes after:
  output<>tls_block cell ->entry_errno_ready cell before ->
  Mem.storebytes before output offset bytes=Some after ->entry_errno_ready cell after.
Proof.
  intros SEPARATE[error[LOW[HIGH[ACCESS LOAD]]]]COPY.
  exists error;unfold initialized_errno;split;[exact LOW|]. split;[exact HIGH|]. split.
  - eapply Mem.storebytes_valid_access_1;eassumption.
  - erewrite Mem.load_storebytes_other;[exact LOAD|exact COPY|left;congruence].
Qed.

Lemma clock_fresh_old_alloc cell base allocated output:
  Mem.alloc base 0 16=(allocated,output) ->clock_old_frame cell base allocated.
Proof. intro ALLOC;eapply Mem.alloc_unchanged_on;exact ALLOC. Qed.

Lemma clock_fresh_old_effect cell base allocated output observation after:
  ~Mem.valid_block base output ->clock_old_frame cell base allocated ->
  process_clock_effect cell output Ptrofs.zero allocated observation after ->clock_old_frame cell base after.
Proof.
  intros FRESH OLD EFFECT;eapply Mem.unchanged_on_trans;[exact OLD|].
  eapply Mem.unchanged_on_implies;[eapply clock_effect_frame;exact EFFECT|].
  intros object position[VALID TLS] VALID_AFTER;split;[left;congruence|exact TLS].
Qed.

Lemma clock_fresh_old_free cell base before output after:
  ~Mem.valid_block base output ->clock_old_frame cell base before ->
  Mem.free before output 0 16=Some after ->clock_old_frame cell base after.
Proof.
  intros FRESH OLD FREE;eapply Mem.unchanged_on_trans;[exact OLD|].
  eapply Mem.free_unchanged_on;[exact FREE|].
  intros position RANGE[VALID TLS];contradiction.
Qed.
