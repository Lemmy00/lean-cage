(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.encoding: Actual typed by-value result copying with arbitrary padding values. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata Ctypes Clight.
Require Import Library ScalarMemory ResultLayout FreshMemory FrameRecord.
Import ListNotations.
Open Scope Z_scope.
Theorem frame_owned_old : forall base after b ofs r digest,
  old_memory base after -> frame_result_owned base b ofs r digest ->
  frame_result_owned after b ofs r digest.
Proof.
  intros base after b ofs r digest OLD [LOW [HIGH [ALIGN [PERMS [LEN [CELLS DIGEST]]]]]].
  split;[exact LOW|]. split;[exact HIGH|]. split;[exact ALIGN|]. split.
  - intros pos RANGE;eapply Mem.perm_unchanged_on;[exact OLD| |apply PERMS;exact RANGE].
    eapply Mem.perm_valid_block;apply PERMS;exact RANGE.
  - split;[exact LEN|]. split.
    + intros cell IN;eapply old_memory_load;[exact OLD|apply CELLS;exact IN].
    + eapply old_memory_readable;eassumption.
Qed.
Theorem frame_copied_contents : forall before after src sofs dst values r digest,
  frame_result_owned before src sofs r digest ->
  Mem.loadbytes before src sofs 144=Some values ->
  Mem.storebytes before dst 0 values=Some after ->
  frame_result_contents after dst 0 r digest /\
  readable_bytes after {|address_block:=dst;address_offset:=108|} digest.
Proof.
  intros before after src sofs dst values r digest
    [LOW [HIGH [ALIGN [PERMS [LEN [CELLS [DB DL]]]]]]] LOAD STORE.
  assert (VLEN : Z.of_nat (length values)=144).
  { rewrite (Mem.loadbytes_length _ _ _ _ _ LOAD);reflexivity. }
  assert (WHOLE : Mem.loadbytes before src sofs (Z.of_nat (length values))=Some values) by (rewrite VLEN;exact LOAD).
  split.
  - intros cell IN.
    pose proof (frame_result_cells_valid r digest) as VALID;rewrite Forall_forall in VALID.
    destruct (VALID cell IN) as [CL [CH CA]].
    eapply copied_scalar_load;[exact WHOLE|exact STORE|exact CL|rewrite VLEN;exact CH|
      cbn;exact CA|apply CELLS;exact IN].
  - split.
    + unfold span_bounds;cbn [address_offset];rewrite LEN;vm_compute;repeat split;discriminate.
    + pose proof (loadbytes_slice _ _ _ _ 108 32 WHOLE ltac:(lia) ltac:(lia) ltac:(rewrite VLEN;lia)) as SUB.
      cbn [address_block address_offset] in DL;rewrite LEN in DL;cbn in DL.
      change (Mem.loadbytes before src (sofs+108) 32=Some (firstn 32 (skipn 108 values))) in SUB.
      assert (PART : firstn 32 (skipn 108 values)=map Byte digest) by congruence.
      pose proof (Mem.loadbytes_storebytes_same _ _ _ _ _ STORE) as FULL.
      pose proof (loadbytes_slice _ _ _ _ 108 32 FULL ltac:(lia) ltac:(lia) ltac:(rewrite VLEN;lia)) as SUB'.
      cbn [address_block address_offset];rewrite LEN;cbn;rewrite <-PART;exact SUB'.
Qed.

Theorem fresh_frame_copy_exists : forall base src sofs r digest,
  frame_result_owned base src sofs r digest ->
  exists allocated local after,
    Mem.alloc base 0 144=(allocated,local) /\
    assign_loc result_ge result_type allocated local Ptrofs.zero Full
      (Vptr src (Ptrofs.repr sofs)) after /\
    old_memory base after /\ frame_result_owned after local 0 r digest /\
    Mem.range_perm after local 0 144 Cur Freeable.
Proof.
  intros base src sofs r digest INPUT.
  pose proof INPUT as [LOW [HIGH [ALIGN [PERMS [LEN REST]]]]].
  destruct (Mem.alloc base 0 144) as [allocated local] eqn:ALLOC.
  assert (FRESH : ~ Mem.valid_block base local) by (eapply Mem.fresh_block_alloc;exact ALLOC).
  assert (OLD : old_memory base allocated) by (eapply Mem.alloc_unchanged_on;exact ALLOC).
  pose proof (frame_owned_old _ _ _ _ _ _ OLD INPUT) as OWN.
  assert (PERMS' : Mem.range_perm allocated src sofs (sofs+144) Cur Readable).
  { exact (proj1 (proj2 (proj2 (proj2 OWN)))). }
  destruct (Mem.range_perm_loadbytes allocated src sofs 144 PERMS') as [values LOAD].
  assert (VLEN : Z.of_nat (length values)=144).
  { rewrite (Mem.loadbytes_length _ _ _ _ _ LOAD);reflexivity. }
  assert (OUT : Mem.range_perm allocated local 0 (0+Z.of_nat (length values)) Cur Writable).
  { rewrite VLEN. intros pos RANGE;eapply Mem.perm_implies;[eapply Mem.perm_alloc_2;eassumption|constructor]. }
  destruct (Mem.range_perm_storebytes _ _ _ _ OUT) as [after STORE].
  assert (OF : old_memory base after).
  { eapply Mem.unchanged_on_trans;[exact OLD|]. eapply Mem.storebytes_unchanged_on;[exact STORE|].
    intros pos RANGE VALID;contradiction. }
  assert (LFREE : Mem.range_perm after local 0 144 Cur Freeable).
  { intros pos RANGE;eapply Mem.perm_storebytes_1;[exact STORE|eapply Mem.perm_alloc_2;eassumption]. }
  assert (NE : src<>local).
  { intro SAME;subst src;apply FRESH;eapply Mem.perm_valid_block with (ofs:=sofs);apply PERMS;lia. }
  assert (REP : Ptrofs.unsigned (Ptrofs.repr sofs)=sofs)
    by (apply Ptrofs.unsigned_repr;unfold Ptrofs.max_unsigned;lia).
  exists allocated,local,after;split;[reflexivity|]. split.
  - eapply assign_loc_copy with (bytes:=values).
    + reflexivity.
    + intros;rewrite REP;exact ALIGN.
    + intros;exists 0;reflexivity.
    + left;exact NE.
    + rewrite REP;exact LOAD.
    + exact STORE.
  - split;[exact OF|]. split;[|exact LFREE].
    destruct (frame_copied_contents _ _ _ _ _ _ _ _ OWN LOAD STORE) as [CELLS DIGEST].
    split;[lia|]. split;[change (144<=18446744073709551616);lia|]. split;[exists 0;reflexivity|]. split.
    + intros pos RANGE;eapply Mem.perm_implies;[apply LFREE;exact RANGE|constructor].
    + split;[exact LEN|]. split;assumption.
Qed.

Theorem frame_copy_into_fresh : forall base before src sofs dst r digest,
  old_memory base before -> ~ Mem.valid_block base dst -> src<>dst ->
  frame_result_owned before src sofs r digest -> Mem.range_perm before dst 0 144 Cur Freeable ->
  exists after, assign_loc result_ge result_type before dst Ptrofs.zero Full
    (Vptr src (Ptrofs.repr sofs)) after /\ old_memory base after /\
    frame_result_owned after dst 0 r digest /\ Mem.range_perm after dst 0 144 Cur Freeable.
Proof.
  intros base before src sofs dst r digest OLD FRESH NE OWN LOCAL.
  pose proof OWN as [LOW [HIGH [ALIGN [PERMS [LEN REST]]]]].
  destruct (Mem.range_perm_loadbytes before src sofs 144 PERMS) as [values LOAD].
  assert (VLEN : Z.of_nat (length values)=144).
  { rewrite (Mem.loadbytes_length _ _ _ _ _ LOAD);reflexivity. }
  assert (WRITE : Mem.range_perm before dst 0 (0+Z.of_nat (length values)) Cur Writable).
  { rewrite VLEN;intros pos RANGE;eapply Mem.perm_implies;[apply LOCAL;exact RANGE|constructor]. }
  destruct (Mem.range_perm_storebytes _ _ _ _ WRITE) as [after STORE].
  assert (OF : old_memory base after).
  { eapply Mem.unchanged_on_trans;[exact OLD|]. eapply Mem.storebytes_unchanged_on;[exact STORE|].
    intros pos RANGE VALID;contradiction. }
  assert (LFREE : Mem.range_perm after dst 0 144 Cur Freeable).
  { intros pos RANGE;eapply Mem.perm_storebytes_1;[exact STORE|apply LOCAL;exact RANGE]. }
  assert (REP : Ptrofs.unsigned (Ptrofs.repr sofs)=sofs)
    by (apply Ptrofs.unsigned_repr;unfold Ptrofs.max_unsigned;lia).
  exists after;split.
  - eapply assign_loc_copy with (bytes:=values).
    + reflexivity.
    + intros;rewrite REP;exact ALIGN.
    + intros;exists 0;reflexivity.
    + left;exact NE.
    + rewrite REP;exact LOAD.
    + exact STORE.
  - split;[exact OF|]. split;[|exact LFREE].
    destruct (frame_copied_contents _ _ _ _ _ _ _ _ OWN LOAD STORE) as [CELLS DIGEST].
    split;[lia|]. split;[change (144<=18446744073709551616);lia|]. split;[exists 0;reflexivity|]. split.
    + intros pos RANGE;eapply Mem.perm_implies;[apply LFREE;exact RANGE|constructor].
    + split;[exact LEN|]. split;assumption.
Qed.
