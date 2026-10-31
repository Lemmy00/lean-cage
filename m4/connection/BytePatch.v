(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.encoding: Exact initialized bytes after bounded overwrites. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata.
Require Import Library ScalarMemory WriteBytes.
Import ListNotations.
Open Scope Z_scope.
Definition patch_bytes (old : list Byte.int) index replacement :=
  firstn index old ++ replacement ++ skipn (index+length replacement) old.
Lemma patch_bytes_length : forall old index replacement,
  (index+length replacement<=length old)%nat -> length (patch_bytes old index replacement)=length old.
Proof. intros;unfold patch_bytes;rewrite !app_length,firstn_length,skipn_length,Nat.min_l;lia. Qed.

Theorem readable_bytes_patch : forall m after p old index replacement,
  readable_bytes m p old -> (index+length replacement<=length old)%nat ->
  Mem.storebytes m (address_block p) (address_offset p+Z.of_nat index) (map Byte replacement)=Some after ->
  readable_bytes after p (patch_bytes old index replacement).
Proof.
  intros m after p old index replacement [BOUNDS LOAD] BOUND STORE.
  split;[unfold span_bounds in *;rewrite patch_bytes_length by exact BOUND;exact BOUNDS|].
  unfold patch_bytes;rewrite !map_app.
  assert (PREFIX : Mem.loadbytes after (address_block p) (address_offset p) (Z.of_nat index)=
    Some (map Byte (firstn index old))).
  { rewrite (Mem.loadbytes_storebytes_other _ _ _ _ _ STORE) by (first [lia|right;left;lia]).
    pose proof (loadbytes_slice m (address_block p) (address_offset p) (map Byte old)
      0 (Z.of_nat index)) as SLICE.
    rewrite map_length in SLICE. specialize (SLICE LOAD ltac:(lia) ltac:(lia) ltac:(lia)).
    rewrite Z.add_0_r,Nat2Z.id in SLICE;cbn [Z.to_nat skipn] in SLICE.
    rewrite firstn_map in SLICE;exact SLICE. }
  assert (SUFFIX : Mem.loadbytes after (address_block p)
    (address_offset p+Z.of_nat (index+length replacement))
    (Z.of_nat (length old-(index+length replacement)))=
    Some (map Byte (skipn (index+length replacement) old))).
  { rewrite (Mem.loadbytes_storebytes_other _ _ _ _ _ STORE).
    - pose proof (loadbytes_slice m (address_block p) (address_offset p) (map Byte old)
        (Z.of_nat (index+length replacement)) (Z.of_nat (length old-(index+length replacement)))) as SLICE.
      rewrite map_length in SLICE;specialize (SLICE LOAD ltac:(lia) ltac:(lia) ltac:(lia)).
      rewrite !Nat2Z.id,skipn_map,firstn_map in SLICE.
      replace (length old-(index+length replacement))%nat with (length (skipn (index+length replacement) old)) in SLICE
        by (rewrite skipn_length;reflexivity).
      rewrite firstn_all,skipn_length in SLICE;exact SLICE.
    - lia.
    - rewrite map_length;right;right;lia. }
  assert (NEW : Mem.loadbytes after (address_block p) (address_offset p+Z.of_nat index)
    (Z.of_nat (length replacement))=Some (map Byte replacement)).
  { rewrite <- (map_length Byte replacement);eapply Mem.loadbytes_storebytes_same;exact STORE. }
  rewrite !app_length,firstn_length,skipn_length,Nat.min_l by lia.
  rewrite !Nat2Z.inj_add.
  eapply Mem.loadbytes_concat;[exact PREFIX| |lia|lia].
  eapply Mem.loadbytes_concat;[exact NEW| |lia|lia].
  replace (address_offset p+Z.of_nat index+Z.of_nat (length replacement)) with
    (address_offset p+Z.of_nat (index+length replacement)) by lia;exact SUFFIX.
Qed.

Theorem byte_writes_patch : forall m after p old index values,
  readable_bytes m p old -> (index+length values<=length old)%nat -> values<>[] ->
  byte_writes m (address_block p) (address_offset p+Z.of_nat index) values after ->
  readable_bytes after p (patch_bytes old index (map (fun x=>Byte.repr (Int.unsigned x)) values)).
Proof.
  intros. eapply readable_bytes_patch;[exact H|rewrite map_length;exact H0|].
  rewrite map_map. exact (byte_writes_storebytes _ _ _ _ _ H2 H1).
Qed.
