(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-decoder.source: Initialized frame subspans and actual reader input ownership. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata Clight.
Require Import Slice Codec IO Library Readers ScalarMemory.
Import ListNotations.
Open Scope Z_scope.

Definition offset_address p n :=
  {|address_block := address_block p; address_offset := address_offset p + Z.of_nat n|}.
Definition byte_at bytes n := nth n bytes Byte.zero.
Definition byte_word_at bytes n := byte_word (byte_at bytes n).
Definition word32_at bytes n := get32_word
  (byte_word_at bytes n) (byte_word_at bytes (n+1))
  (byte_word_at bytes (n+2)) (byte_word_at bytes (n+3)).
Definition word64_at bytes n := get64_word
  (byte_word_at bytes n) (byte_word_at bytes (n+1))
  (byte_word_at bytes (n+2)) (byte_word_at bytes (n+3))
  (byte_word_at bytes (n+4)) (byte_word_at bytes (n+5))
  (byte_word_at bytes (n+6)) (byte_word_at bytes (n+7)).

Lemma subspan_length : forall (A : Type) (bytes : list A) start count,
  (start + count <= length bytes)%nat ->
  length (firstn count (skipn start bytes)) = count.
Proof. intros; rewrite firstn_length, skipn_length, Nat.min_l; lia. Qed.

Theorem readable_subspan : forall m p bytes start count,
  readable_bytes m p bytes -> (start < length bytes)%nat ->
  (start + count <= length bytes)%nat ->
  readable_bytes m (offset_address p start) (firstn count (skipn start bytes)).
Proof.
  intros m p bytes start count [[BASE [END SIZE]] LOAD] START BOUND.
  pose proof (subspan_length _ bytes start count BOUND) as LEN.
  split.
  - unfold span_bounds. change (0 <= address_offset p + Z.of_nat start < Ptrofs.modulus /\ address_offset p + Z.of_nat start + Z.of_nat (length (firstn count (skipn start bytes))) <= Ptrofs.modulus /\ Z.of_nat (length (firstn count (skipn start bytes))) <= Int64.max_unsigned). rewrite LEN. repeat split; lia.
  - change (Mem.loadbytes m (address_block p) (address_offset p + Z.of_nat start) (Z.of_nat (length (firstn count (skipn start bytes)))) = Some (map Byte (firstn count (skipn start bytes)))). rewrite LEN.
    pose proof (loadbytes_slice m (address_block p) (address_offset p) (map Byte bytes)
      (Z.of_nat start) (Z.of_nat count)) as SLICE.
    rewrite map_length in SLICE.
    specialize (SLICE LOAD ltac:(lia) ltac:(lia) ltac:(lia)).
    rewrite Nat2Z.id, Nat2Z.id, skipn_map, firstn_map in SLICE.
    exact SLICE.
Qed.

Lemma one_byte_slice : forall (A : Type) (bytes : list A) n default,
  (n < length bytes)%nat -> firstn 1 (skipn n bytes) = [nth n bytes default].
Proof.
  intros A bytes; induction bytes as [|b bytes IH]; intros n default BOUND;
    destruct n; cbn in *; try lia; auto.
  apply IH; lia.
Qed.

Theorem readable_byte_load : forall m p bytes n,
  readable_bytes m p bytes -> (n < length bytes)%nat ->
  Mem.loadv Mint8unsigned m (address_value (offset_address p n)) =
    Some (Vint (byte_word_at bytes n)).
Proof.
  intros m p bytes n READ BOUND.
  pose proof (readable_subspan m p bytes n 1 READ BOUND ltac:(lia)) as SUB.
  rewrite (one_byte_slice _ bytes n Byte.zero BOUND) in SUB.
  destruct SUB as [[BASE [END SIZE]] LOAD].
  unfold address_value, Mem.loadv. rewrite Ptrofs.unsigned_repr by
    (unfold Ptrofs.max_unsigned; lia).
  destruct (zle (address_offset (offset_address p n) + size_chunk Mint8unsigned) Ptrofs.modulus);
    [|cbn in *; lia].
  unfold byte_word_at, byte_at. rewrite <- decode_byte.
  eapply Mem.loadbytes_load; [exact LOAD|apply Z.divide_1_l].
Qed.

Lemma offset_pointer_add : forall p n i,
  Ptrofs.add (Ptrofs.repr (address_offset p + Z.of_nat n)) (Ptrofs.repr (Z.of_nat i)) =
    Ptrofs.repr (address_offset p + Z.of_nat (n+i)).
Proof.
  intros. unfold Ptrofs.add. apply Ptrofs.eqm_samerepr.
  replace (address_offset p + Z.of_nat (n+i)) with
    ((address_offset p + Z.of_nat n) + Z.of_nat i) by lia.
  apply Ptrofs.eqm_add; apply Ptrofs.eqm_sym; apply Ptrofs.eqm_unsigned_repr.
Qed.

Lemma span_reader_load : forall m p bytes n i,
  readable_bytes m p bytes -> (n+i < length bytes)%nat ->
  Mem.loadv Mint8unsigned m (Vptr (address_block p)
    (Ptrofs.add (Ptrofs.repr (address_offset p + Z.of_nat n)) (Ptrofs.repr (Z.of_nat i)))) =
    Some (Vint (byte_word_at bytes (n+i))).
Proof. intros. rewrite offset_pointer_add. apply readable_byte_load; assumption. Qed.

Theorem frame_reader32_input : forall m p bytes n,
  readable_bytes m p bytes -> (n+4 <= length bytes)%nat ->
  reader_input m (address_block p) (Ptrofs.repr (address_offset p + Z.of_nat n))
    f_get32 (Vint (word32_at bytes n)) 59.
Proof.
  intros m p bytes n READ BOUND. pose proof READ as [[BASE [END SIZE]] LOAD].
  unfold word32_at. apply input32.
  - rewrite Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; lia); lia.
  - unfold loads32. repeat split.
    + pose proof (span_reader_load m p bytes n 0 READ ltac:(lia)) as FIRST.
      rewrite Nat.add_0_r in FIRST; exact FIRST.
    + exact (span_reader_load m p bytes n 1 READ ltac:(lia)).
    + exact (span_reader_load m p bytes n 2 READ ltac:(lia)).
    + exact (span_reader_load m p bytes n 3 READ ltac:(lia)).
Qed.

Theorem frame_reader64_input : forall m p bytes n,
  readable_bytes m p bytes -> (n+8 <= length bytes)%nat ->
  reader_input m (address_block p) (Ptrofs.repr (address_offset p + Z.of_nat n))
    f_get64 (Vlong (word64_at bytes n)) 103.
Proof.
  intros m p bytes n READ BOUND. pose proof READ as [[BASE [END SIZE]] LOAD].
  unfold word64_at. apply input64.
  - rewrite Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; lia); lia.
  - split.
    + unfold loads32. repeat split.
      * pose proof (span_reader_load m p bytes n 0 READ ltac:(lia)) as FIRST.
        rewrite Nat.add_0_r in FIRST; exact FIRST.
      * exact (span_reader_load m p bytes n 1 READ ltac:(lia)).
      * exact (span_reader_load m p bytes n 2 READ ltac:(lia)).
      * exact (span_reader_load m p bytes n 3 READ ltac:(lia)).
    + repeat split.
      * exact (span_reader_load m p bytes n 4 READ ltac:(lia)).
      * exact (span_reader_load m p bytes n 5 READ ltac:(lia)).
      * exact (span_reader_load m p bytes n 6 READ ltac:(lia)).
      * exact (span_reader_load m p bytes n 7 READ ltac:(lia)).
Qed.

Lemma pointer_offset_add : forall p n,
  Ptrofs.add (Ptrofs.repr (address_offset p)) (Ptrofs.repr (Z.of_nat n)) =
    Ptrofs.repr (address_offset p + Z.of_nat n).
Proof.
  intros. pose proof (offset_pointer_add p 0 n) as ADD.
  cbn [Nat.add Z.of_nat] in ADD. rewrite Z.add_0_r in ADD; exact ADD.
Qed.

Lemma pointer_add_representations : forall a b,
  Ptrofs.add (Ptrofs.repr a) (Ptrofs.repr b) = Ptrofs.repr (a+b).
Proof.
  intros. unfold Ptrofs.add. apply Ptrofs.eqm_samerepr.
  apply Ptrofs.eqm_add; apply Ptrofs.eqm_sym; apply Ptrofs.eqm_unsigned_repr.
Qed.
