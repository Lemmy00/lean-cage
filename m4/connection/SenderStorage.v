(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.memory: Preserve old objects and both live local allocations during encoding. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata.
Require Import Library WriteBytes FreshMemory FrameRecord BytePatch.
Import ListNotations.
Open Scope Z_scope.
Definition sender_storage base result_local bytes_local r digest bytes m :=
  old_memory base m /\ frame_result_owned m result_local 0 r digest /\
  readable_bytes m {|address_block:=bytes_local;address_offset:=0|} bytes /\
  Mem.range_perm m result_local 0 144 Cur Freeable /\
  Mem.range_perm m bytes_local 0 160 Cur Freeable.

Lemma fresh_partial_copy_old : forall base m local offset bytes schedule after,
  ~ Mem.valid_block base local -> old_memory base m ->
  partial_copy {|address_block:=local;address_offset:=offset|} bytes m schedule after ->
  old_memory base after.
Proof.
  intros base m local offset bytes schedule after FRESH OLD RUN.
  eapply Mem.unchanged_on_trans;[exact OLD|].
  eapply Mem.unchanged_on_implies;[eapply partial_copy_outside;exact RUN|].
  intros b pos VALID VALIDM;left;cbn;congruence.
Qed.

Theorem sender_storage_patch : forall base m after result_local bytes_local r digest bytes index replacement,
  ~ Mem.valid_block base bytes_local -> result_local<>bytes_local ->
  sender_storage base result_local bytes_local r digest bytes m ->
  (index+length replacement<=length bytes)%nat ->
  Mem.storebytes m bytes_local (Z.of_nat index) (map Byte replacement)=Some after ->
  sender_storage base result_local bytes_local r digest (patch_bytes bytes index replacement) after.
Proof.
  intros base m after result_local bytes_local r digest bytes index replacement FRESH NE
    [OLD [OWN [READ [RFREE BFREE]]]] BOUND STORE.
  assert (OUTSIDE : Mem.unchanged_on (fun b _=>b<>bytes_local) m after).
  { eapply Mem.storebytes_unchanged_on;[exact STORE|]. intros pos RANGE SAME;apply SAME;reflexivity. }
  split.
  - eapply Mem.unchanged_on_trans;[exact OLD|].
    eapply Mem.unchanged_on_implies;[exact OUTSIDE|]. intros;congruence.
  - split.
    + destruct OWN as [LOW [HIGH [ALIGN [PERMS [LEN [CONTENTS [DB DL]]]]]]].
      split;[exact LOW|]. split;[exact HIGH|]. split;[exact ALIGN|]. split.
      * intros pos RANGE;eapply Mem.perm_storebytes_1;[exact STORE|apply PERMS;exact RANGE].
      * split;[exact LEN|]. split.
        -- intros cell IN;eapply Mem.load_unchanged_on;[exact OUTSIDE|intros;exact NE|apply CONTENTS;exact IN].
        -- split;[exact DB|]. eapply Mem.loadbytes_unchanged_on;[exact OUTSIDE|intros;exact NE|exact DL].
    + split.
      * eapply readable_bytes_patch;[exact READ|exact BOUND|exact STORE].
      * split;intros pos RANGE;eapply Mem.perm_storebytes_1;[exact STORE|apply RFREE;exact RANGE|exact STORE|apply BFREE;exact RANGE].
Qed.

Theorem sender_storage_writes : forall base m after result_local bytes_local r digest bytes index values,
  ~ Mem.valid_block base bytes_local -> result_local<>bytes_local ->
  sender_storage base result_local bytes_local r digest bytes m ->
  (index+length values<=length bytes)%nat -> values<>[] ->
  byte_writes m bytes_local (Z.of_nat index) values after ->
  sender_storage base result_local bytes_local r digest
    (patch_bytes bytes index (map (fun x=>Byte.repr (Int.unsigned x)) values)) after.
Proof.
  intros. eapply sender_storage_patch;[exact H|exact H0|exact H1|rewrite map_length;exact H2|].
  rewrite map_map;exact (byte_writes_storebytes _ _ _ _ _ H4 H3).
Qed.
