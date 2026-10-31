(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.input: Allocate independent arbitrary fields and digest without assuming a completed sender. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata.
Require Import Library ScalarMemory ResultLayout Readers Codec FrameBytes FreshMemory FrameRecord.
Import ListNotations.
Open Scope Z_scope.
Definition frame_scalar_fields r := firstn 18 (frame_result_cells r []).
Lemma frame_scalar_layout : forall r digest,frame_result_cells r digest=
  frame_scalar_fields r++map (frame_digest_cell digest) (seq 0 32).
Proof. reflexivity. Qed.
Lemma frame_scalar_fields_valid : forall r,Forall (scalar_valid 108) (frame_scalar_fields r).
Proof. intros;apply scalar_list_validb_sound;reflexivity. Qed.
Lemma frame_scalar_fields_separate : forall r before cell rest,
  frame_scalar_fields r=before++cell::rest -> Forall (scalar_separate cell) rest.
Proof. intros;eapply (scalar_orderedb_sound (frame_scalar_fields r));[reflexivity|exact H]. Qed.
Lemma frame_byte_normalized : forall b,Int.zero_ext 8 (Int.repr (Byte.unsigned b))=byte_word b.
Proof.
  intros b;rewrite <- (Int.repr_unsigned (Int.zero_ext 8 (Int.repr (Byte.unsigned b)))).
  rewrite Int.zero_ext_mod by (change (0<=8<32);lia).
  pose proof (Byte.unsigned_range b) as RANGE;change (0<=Byte.unsigned b<256) in RANGE.
  rewrite Int.unsigned_repr by (change (0<=Byte.unsigned b<=4294967295);lia).
  change (Int.repr (Byte.unsigned b mod 256)=byte_word b).
  rewrite Z.mod_small;[reflexivity|exact RANGE].
Qed.
Lemma frame_digest_readable_cells : forall m b digest,
  length digest=32%nat -> readable_bytes m {|address_block:=b;address_offset:=108|} digest ->
  forall cell,In cell (map (frame_digest_cell digest) (seq 0 32)) ->
    Mem.load (scalar_chunk cell) m b (scalar_offset cell)=
      Some (Val.load_result (scalar_chunk cell) (scalar_value cell)).
Proof.
  intros m b digest LEN READ cell IN;apply in_map_iff in IN;destruct IN as [n [EQ IN]];subst cell.
  apply in_seq in IN.
  pose proof (readable_subspan _ _ _ n 1 READ ltac:(rewrite LEN;lia) ltac:(rewrite LEN;lia)) as SUB.
  rewrite (one_byte_slice _ digest n Byte.zero ltac:(rewrite LEN;lia)) in SUB.
  destruct SUB as [BOUNDS LOAD]. cbn [offset_address address_offset address_block] in LOAD.
  cbn [frame_digest_cell scalar_chunk scalar_offset scalar_value Val.load_result].
  rewrite frame_byte_normalized.
  rewrite <- decode_byte.
  eapply Mem.loadbytes_load;[exact LOAD|apply Z.divide_1_l].
Qed.
Theorem allocate_frame_record : forall base r digest,
  length digest=32%nat -> exists after b,
    old_memory base after /\ frame_result_owned after b 0 r digest /\
    b=Mem.nextblock base.
Proof.
  intros base r digest LEN.
  destruct (Mem.alloc base 0 144) as [allocated b] eqn:ALLOC.
  assert (FRESH : ~Mem.valid_block base b) by (eapply Mem.fresh_block_alloc;exact ALLOC).
  assert (DIGESTWRITE : Mem.range_perm allocated b 108 (108+Z.of_nat (length (map Byte digest))) Cur Writable).
  { rewrite map_length,LEN;intros pos RANGE;eapply Mem.perm_implies;
      [eapply Mem.perm_alloc_2;[exact ALLOC|cbn in *;lia]|constructor]. }
  destruct (Mem.range_perm_storebytes _ _ _ _ DIGESTWRITE) as [withdigest DIGEST].
  assert (PERMS : Mem.range_perm withdigest b 0 144 Cur Freeable).
  { intros pos RANGE;eapply Mem.perm_storebytes_1;[exact DIGEST|eapply Mem.perm_alloc_2;eassumption]. }
  destruct (scalar_stores_exist b 108 (frame_scalar_fields r) withdigest (frame_scalar_fields_valid r))
    as [after STORES].
  { intros pos RANGE;apply PERMS;lia. }
  pose proof (scalar_stores_outside _ _ _ _ _ STORES (frame_scalar_fields_valid r)) as OUTSIDE.
  assert (OLD : old_memory base after).
  { eapply Mem.unchanged_on_trans;[eapply Mem.alloc_unchanged_on;exact ALLOC|].
    eapply Mem.unchanged_on_trans.
    - eapply Mem.storebytes_unchanged_on;[exact DIGEST|]. intros pos RANGE VALID;contradiction.
    - eapply Mem.unchanged_on_implies;[exact OUTSIDE|]. intros block pos VALID VALIDALLOC;left;congruence. }
  assert (READ : readable_bytes after {|address_block:=b;address_offset:=108|} digest).
  { split.
    - unfold span_bounds;cbn [address_offset];rewrite LEN.
      change (0<=108<18446744073709551616 /\ 108+32<=18446744073709551616 /\ 32<=18446744073709551615);lia.
    - cbn [address_block address_offset]. rewrite <- (map_length Byte digest).
      eapply Mem.loadbytes_unchanged_on;[exact OUTSIDE|intros;right;right;lia|].
      exact (Mem.loadbytes_storebytes_same _ _ _ _ _ DIGEST). }
  exists after,b;split;[exact OLD|]. split;[|exact (Mem.alloc_result _ _ _ _ _ ALLOC)].
  split;[lia|]. split;[change (144<=18446744073709551616);lia|]. split;[exists 0;reflexivity|]. split.
  - intros pos RANGE;eapply Mem.perm_implies;[apply (scalar_stores_permissions _ _ _ _ STORES);apply PERMS;exact RANGE|constructor].
  - split;[exact LEN|]. split;[|exact READ]. intros cell IN;rewrite frame_scalar_layout in IN.
    apply in_app_iff in IN;destruct IN as [IN|IN].
    + cbn [Z.add];eapply scalar_stores_fields;[exact STORES|apply frame_scalar_fields_separate|exact IN].
    + cbn [Z.add];eapply frame_digest_readable_cells;[exact LEN|exact READ|exact IN].
Qed.
