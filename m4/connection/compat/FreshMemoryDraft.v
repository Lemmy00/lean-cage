(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-callers.control: Independently allocated local bytes preserve old owned state. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata.
Require Import Machine WriteBytes Library ProcessEffects.
Import ListNotations.
Open Scope Z_scope.

Definition old_memory base after := Mem.unchanged_on (fun b _ => Mem.valid_block base b) base after.

Lemma fresh_writes_preserve_old : forall base m local ofs values after,
  ~ Mem.valid_block base local -> old_memory base m ->
  byte_writes m local ofs values after -> old_memory base after.
Proof.
  intros base m local ofs values after FRESH OLD WRITES.
  eapply Mem.unchanged_on_trans; [exact OLD|].
  eapply Mem.unchanged_on_implies; [eapply byte_writes_outside; exact WRITES|].
  intros b pos VALID VALIDM. left; congruence.
Qed.

Lemma fresh_writer_prefix_preserves_old : forall base m local ofs values after,
  ~ Mem.valid_block base local -> old_memory base m ->
  writer_prefix m local ofs values after -> old_memory base after.
Proof.
  intros base m local ofs values after FRESH OLD [first [rest [ES WRITES]]].
  eapply fresh_writes_preserve_old; eassumption.
Qed.

Lemma old_memory_readable : forall base after p bytes,
  old_memory base after -> readable_bytes base p bytes -> readable_bytes after p bytes.
Proof.
  intros base after p bytes OLD [BOUNDS LOAD]; split; [exact BOUNDS|].
  eapply Mem.loadbytes_unchanged_on; [exact OLD| |exact LOAD].
  intros pos RANGE. eapply Mem.perm_valid_block.
  eapply Mem.loadbytes_range_perm; [exact LOAD|exact RANGE].
Qed.

Lemma old_memory_string : forall base after p bytes,
  old_memory base after -> c_string base p bytes -> c_string after p bytes.
Proof. intros base after p bytes OLD [NONZERO READ]; split; [exact NONZERO|eapply old_memory_readable; eassumption]. Qed.

Lemma old_memory_load : forall base after chunk b ofs value,
  old_memory base after -> Mem.load chunk base b ofs = Some value ->
  Mem.load chunk after b ofs = Some value.
Proof.
  intros base after chunk b ofs value OLD LOAD.
  eapply Mem.load_unchanged_on; [exact OLD| |exact LOAD].
  intros pos RANGE. eapply Mem.perm_valid_block.
  pose proof (Mem.load_valid_access _ _ _ _ _ LOAD) as [PERM ALIGN].
  apply PERM; exact RANGE.
Qed.

Lemma old_memory_tls : forall base after cell,
  old_memory base after -> tls_ready cell base -> tls_ready cell after.
Proof.
  intros base after cell OLD [LOW [HIGH [PERM ALIGN]]].
  split; [exact LOW|]. split; [exact HIGH|]. split; [|exact ALIGN].
  intros pos RANGE. eapply Mem.perm_unchanged_on; [exact OLD| |apply PERM; exact RANGE].
  eapply Mem.perm_valid_block; apply PERM; exact RANGE.
Qed.
