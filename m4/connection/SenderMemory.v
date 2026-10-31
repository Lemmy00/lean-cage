(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.encoding: Derive sender allocation, parameter copy and frame initialization. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events Ctypes Ctypesdefs Clight.
Require Import Slice Machine WriteBytes StoreSteps Library FreshMemory ResultLayout WriteAll
  FrameRecord FrameCopy SenderSource SenderZeros.
Import ListNotations.
Open Scope Z_scope.
Lemma frame_owned_after_byte_writes : forall m after b ofs r digest buffer pos values,
  frame_result_owned m b ofs r digest -> b<>buffer -> byte_writes m buffer pos values after ->
  frame_result_owned after b ofs r digest.
Proof.
  intros m after b ofs r digest buffer pos values [LOW [HIGH [ALIGN [PERMS [LEN [CELLS [DB DL]]]]]]] NE WRITES.
  pose proof (byte_writes_outside _ _ _ _ _ WRITES) as OUTSIDE.
  split;[exact LOW|]. split;[exact HIGH|]. split;[exact ALIGN|]. split.
  - intros x RANGE;apply (byte_writes_permissions _ _ _ _ _ WRITES);apply PERMS;exact RANGE.
  - split;[exact LEN|]. split.
    + intros cell IN;eapply Mem.load_unchanged_on;[exact OUTSIDE| |apply CELLS;exact IN].
      intros;left;exact NE.
    + split;[exact DB|]. eapply Mem.loadbytes_unchanged_on;[exact OUTSIDE| |exact DL].
      intros;left;exact NE.
Qed.
Lemma result_copy_permissions : forall before after dst src ofs,
  assign_loc result_ge result_type before dst Ptrofs.zero Full (Vptr src ofs) after ->
  forall b pos kind permission, Mem.perm after b pos kind permission <-> Mem.perm before b pos kind permission.
Proof.
  intros before after dst src ofs COPY;inversion COPY;subst;try discriminate;intros.
  split;[eapply Mem.perm_storebytes_2|eapply Mem.perm_storebytes_1];eassumption.
Qed.
Theorem sender_preparation_exists : forall base fd sequence input ofs r digest k,
  frame_result_owned base input ofs r digest ->
  exists first result_local allocated bytes_local final count,
    Mem.alloc base 0 144=(first,result_local) /\ Mem.alloc first 0 160=(allocated,bytes_local) /\
    store_path result_ge (old_memory base) (sender_initial fd sequence input ofs k base) count
      (State f_send_frame sender_after_zero k (sender_env result_local bytes_local)
        (sender_temps fd sequence input ofs) final) /\
    old_memory base final /\ frame_result_owned final result_local 0 r digest /\
    readable_bytes final {|address_block:=bytes_local;address_offset:=0|} (repeat Byte.zero 160) /\
    Mem.range_perm final result_local 0 144 Cur Freeable /\
    Mem.range_perm final bytes_local 0 160 Cur Freeable.
Proof.
  intros base fd sequence input ofs r digest k INPUT.
  pose proof INPUT as [LOW [HIGH [ALIGN [PERMS REST]]]].
  destruct (Mem.alloc base 0 144) as [first result_local] eqn:A1.
  destruct (Mem.alloc first 0 160) as [allocated bytes_local] eqn:A2.
  assert (FR : ~ Mem.valid_block base result_local) by (eapply Mem.fresh_block_alloc;exact A1).
  assert (FB1 : ~ Mem.valid_block first bytes_local) by (eapply Mem.fresh_block_alloc;exact A2).
  assert (FB : ~ Mem.valid_block base bytes_local).
  { intro VALID;apply FB1;eapply Mem.valid_block_alloc;[exact A1|exact VALID]. }
  assert (RANGE1 : Mem.range_perm first result_local 0 144 Cur Freeable)
    by (intros pos BOUND;eapply Mem.perm_alloc_2;eassumption).
  assert (NE : result_local<>bytes_local).
  { intro SAME;subst bytes_local;apply FB1;eapply Mem.perm_valid_block with (ofs:=0);apply RANGE1;lia. }
  assert (PA : old_memory base allocated).
  { eapply Mem.unchanged_on_trans;[eapply Mem.alloc_unchanged_on;exact A1|eapply Mem.alloc_unchanged_on;exact A2]. }
  assert (RANGE2 : Mem.range_perm allocated result_local 0 144 Cur Freeable)
    by (intros pos BOUND;eapply Mem.perm_alloc_1;[exact A2|apply RANGE1;exact BOUND]).
  assert (BRANGE : Mem.range_perm allocated bytes_local 0 160 Cur Freeable)
    by (intros pos BOUND;eapply Mem.perm_alloc_2;eassumption).
  assert (INR : input<>result_local).
  { intro SAME;subst input;apply FR;eapply Mem.perm_valid_block with (ofs:=ofs);apply PERMS;lia. }
  pose proof (frame_owned_old _ _ _ _ _ _ PA INPUT) as OWN.
  destruct (frame_copy_into_fresh base allocated input ofs result_local r digest PA FR INR OWN RANGE2)
    as [copied [COPY [PC [CONTENTS RFREE]]]].
  assert (BC : Mem.range_perm copied bytes_local 0 160 Cur Freeable).
  { intros pos BOUND;apply (result_copy_permissions _ _ _ _ _ COPY);apply BRANGE;exact BOUND. }
  destruct (byte_writes_exists (repeat Int.zero 160) copied bytes_local 0) as [final WRITES].
  { rewrite repeat_length;change (Mem.range_perm copied bytes_local 0 160 Cur Writable).
    intros pos BOUND;eapply Mem.perm_implies;[apply BC;exact BOUND|constructor]. }
  assert (PF : old_memory base final) by (eapply fresh_writes_preserve_old;[exact FB|exact PC|exact WRITES]).
  destruct (sender_zero_sequence_path (old_memory base) result_local bytes_local
    (sender_temps fd sequence input ofs) k sender_after_zero 160 0 copied final ltac:(lia) WRITES PC)
    as [count PATH].
  { intros before next pos OLD STORE;eapply Mem.unchanged_on_trans;[exact OLD|].
    eapply Mem.store_unchanged_on;[exact STORE|]. intros x RANGE VALID;contradiction. }
  exists first,result_local,allocated,bytes_local,final,(S (S (S (S count)))).
  split;[reflexivity|]. split;[exact A2|]. split.
  - eapply store_next;[apply Mem.unchanged_on_refl|eapply sender_source_entry;[exact A1|exact A2]|].
    rewrite sender_body_parts.
    eapply store_next;[exact PA|apply unchanged_store_edge;WriteAll.structural|].
    eapply store_next;[exact PA|apply sender_parameter_copy_edge;exact COPY|].
    eapply store_next;[exact PC|apply unchanged_store_edge;WriteAll.structural|exact PATH].
  - split;[exact PF|]. split.
    + eapply frame_owned_after_byte_writes;[exact CONTENTS|exact NE|exact WRITES].
    + split.
      * split.
        -- unfold span_bounds;cbn [address_offset];rewrite repeat_length;vm_compute;repeat split;discriminate.
        -- cbn [address_block address_offset]. rewrite repeat_length.
           pose proof (byte_writes_content _ _ _ _ _ WRITES ltac:(discriminate)) as LOAD.
           rewrite repeat_length,map_repeat in LOAD. rewrite map_repeat. exact LOAD.
      * split;intros pos BOUND;apply (byte_writes_permissions _ _ _ _ _ WRITES);[apply RFREE|apply BC];exact BOUND.
Qed.
