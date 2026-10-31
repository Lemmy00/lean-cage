(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-effects.writers: Bit-exact codecs and composition of actual source calls. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events
  Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Slice Codec Machine ClightSteps WriteMemory Deterministic Readers
  StoreSteps WriteBytes Writers.
Import ListNotations.
Open Scope Z_scope.

Lemma put32_bits : forall x j i,
  0 <= j < 4 -> 0 <= i < 32 ->
  Int.testbit (Int.shl (put32_byte x j) (Int.repr (8 * j))) i =
    if zlt i (8 * j) then false else
    if zlt i (8 * j + 8) then Int.testbit x i else false.
Proof.
  intros x j i J I. rewrite Int.bits_shl by exact I.
  rewrite Int.unsigned_repr by (change (0 <= 8*j <= 4294967295); lia).
  destruct (zlt i (8*j)); [reflexivity|]. unfold put32_byte.
  rewrite Int.bits_zero_ext by lia. destruct (zlt (i - 8*j) 8).
  - rewrite zlt_true by lia. rewrite Int.bits_shru by (change (0 <= i-8*j < 32); lia).
    rewrite Int.unsigned_repr by (change (0 <= 8*j <= 4294967295); lia).
    replace (i-8*j+8*j) with i by lia. rewrite zlt_true by exact (proj2 I). reflexivity.
  - rewrite zlt_false by lia. reflexivity.
Qed.

Theorem put_get32_word : forall x,
  get32_word (put32_byte x 0) (put32_byte x 1) (put32_byte x 2) (put32_byte x 3) = x.
Proof.
  intros x. apply Int.same_bits_eq; intros i I. change (0 <= i < 32) in I.
  unfold get32_word. rewrite !Int.bits_or by exact I. rewrite Int.bits_zero.
  change (Int.repr 0) with (Int.repr (8*0)).
  change (Int.repr 8) with (Int.repr (8*1)).
  change (Int.repr 16) with (Int.repr (8*2)).
  change (Int.repr 24) with (Int.repr (8*3)).
  rewrite !put32_bits by lia.
  repeat match goal with |- context [if zlt ?a ?b then _ else _] =>
    destruct (zlt a b); try lia end; cbn; repeat rewrite orb_false_r; reflexivity.
Qed.

Lemma widen_byte_bits : forall y i,
  0 <= i < 64 ->
  Int64.testbit (Int64.repr (Int.unsigned (Int.zero_ext 8 (Int.repr (Int64.unsigned y))))) i =
    if zlt i 8 then Int64.testbit y i else false.
Proof.
  intros y i I. rewrite Int64.testbit_repr by exact I.
  change (Int.testbit (Int.zero_ext 8 (Int.repr (Int64.unsigned y))) i =
    if zlt i 8 then Int64.testbit y i else false).
  rewrite Int.bits_zero_ext by lia. destruct (zlt i 8); [|reflexivity].
  rewrite Int.testbit_repr by (change (0 <= i < 32); lia). reflexivity.
Qed.

Lemma put64_bits : forall x j i,
  0 <= j < 8 -> 0 <= i < 64 ->
  Int64.testbit (Int64.shl (Int64.repr (Int.unsigned (put64_byte x j)))
      (Int64.repr (8 * j))) i =
    if zlt i (8 * j) then false else
    if zlt i (8 * j + 8) then Int64.testbit x i else false.
Proof.
  intros x j i J I. rewrite Int64.bits_shl by exact I.
  rewrite Int64.unsigned_repr by (change (0 <= 8*j <= 18446744073709551615); lia).
  destruct (zlt i (8*j)); [reflexivity|]. unfold put64_byte.
  rewrite widen_byte_bits by lia. destruct (zlt (i - 8*j) 8).
  - rewrite zlt_true by lia. rewrite Int64.bits_shru by (change (0 <= i-8*j < 64); lia).
    rewrite Int64.unsigned_repr by (change (0 <= 8*j <= 18446744073709551615); lia).
    replace (i-8*j+8*j) with i by lia. rewrite zlt_true by exact (proj2 I). reflexivity.
  - rewrite zlt_false by lia. reflexivity.
Qed.

Theorem put_get64_word : forall x,
  get64_word (put64_byte x 0) (put64_byte x 1) (put64_byte x 2) (put64_byte x 3)
    (put64_byte x 4) (put64_byte x 5) (put64_byte x 6) (put64_byte x 7) = x.
Proof.
  intros x. apply Int64.same_bits_eq; intros i I. change (0 <= i < 64) in I.
  unfold get64_word. rewrite !Int64.bits_or by exact I. rewrite Int64.bits_zero.
  change (Int64.repr 0) with (Int64.repr (8*0)).
  change (Int64.repr 8) with (Int64.repr (8*1)).
  change (Int64.repr 16) with (Int64.repr (8*2)).
  change (Int64.repr 24) with (Int64.repr (8*3)).
  change (Int64.repr 32) with (Int64.repr (8*4)).
  change (Int64.repr 40) with (Int64.repr (8*5)).
  change (Int64.repr 48) with (Int64.repr (8*6)).
  change (Int64.repr 56) with (Int64.repr (8*7)).
  rewrite !put64_bits by lia.
  repeat match goal with |- context [if zlt ?a ?b then _ else _] =>
    destruct (zlt a b); try lia end; cbn; repeat rewrite orb_false_r; reflexivity.
Qed.

Lemma encoded_suffix_load : forall m b ofs first rest,
  Mem.loadbytes m b ofs (Z.of_nat (length (first ++ rest))) =
    Some (map byte_encoding (first ++ rest)) ->
  Mem.loadbytes m b (ofs + Z.of_nat (length first)) (Z.of_nat (length rest)) =
    Some (map byte_encoding rest).
Proof.
  intros m b ofs first rest LOAD. rewrite app_length, Nat2Z.inj_add, map_app in LOAD.
  destruct (Mem.loadbytes_split _ _ _ _ _ _ LOAD) as [a [c [A [C EQ]]]]; try lia.
  assert (LEN : length a = length (map byte_encoding first)).
  { erewrite Mem.loadbytes_length by exact A. rewrite Nat2Z.id, map_length; reflexivity. }
  destruct (append_same_length _ a c (map byte_encoding first) (map byte_encoding rest)
    LEN (eq_sym EQ)); subst; assumption.
Qed.

Lemma encoded_head_load : forall m b ofs x rest,
  Mem.loadbytes m b ofs (Z.of_nat (length (x :: rest))) =
    Some (map byte_encoding (x :: rest)) ->
  Mem.load Mint8unsigned m b ofs = Some (Vint (Int.zero_ext 8 x)).
Proof.
  intros m b ofs x rest LOAD.
  replace (Z.of_nat (length (x :: rest))) with (1 + Z.of_nat (length rest)) in LOAD
    by (simpl length; rewrite Nat2Z.inj_succ; lia).
  destruct (Mem.loadbytes_split _ _ _ _ _ _ LOAD) as [a [c [A [C EQ]]]]; try lia.
  assert (LEN : length a = length [byte_encoding x]).
  { erewrite Mem.loadbytes_length by exact A. reflexivity. }
  destruct (append_same_length _ a c [byte_encoding x] (map byte_encoding rest)
    LEN (eq_sym EQ)); subst.
  pose proof (decode_encode_val_general (Vint x) Mint8unsigned Mint8unsigned) as DECODE.
  change (decode_val Mint8unsigned [byte_encoding x] = Vint (Int.zero_ext 8 x)) in DECODE.
  rewrite <- DECODE. eapply Mem.loadbytes_load; [exact A|apply Z.divide_1_l].
Qed.

Lemma encoded_byte_load : forall m b ofs first x rest,
  Ptrofs.unsigned ofs + Z.of_nat (length first) + 1 <= Ptrofs.modulus ->
  Mem.loadbytes m b (Ptrofs.unsigned ofs) (Z.of_nat (length (first ++ x :: rest))) =
    Some (map byte_encoding (first ++ x :: rest)) ->
  Mem.loadv Mint8unsigned m
    (Vptr b (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat (length first))))) =
    Some (Vint (Int.zero_ext 8 x)).
Proof.
  intros m b ofs first x rest BOUND LOAD.
  pose proof (encoded_suffix_load _ _ _ _ _ LOAD) as SUFFIX.
  pose proof (encoded_head_load _ _ _ _ _ SUFFIX) as SINGLE.
  assert (U : Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr (Z.of_nat (length first)))) =
      Ptrofs.unsigned ofs + Z.of_nat (length first)).
  { rewrite Ptrofs.add_unsigned.
    rewrite (Ptrofs.unsigned_repr (Z.of_nat (length first))) by
      (pose proof (Ptrofs.unsigned_range ofs); unfold Ptrofs.max_unsigned; lia).
    rewrite Ptrofs.unsigned_repr; [reflexivity|].
    pose proof (Ptrofs.unsigned_range ofs); unfold Ptrofs.max_unsigned; lia. }
  unfold Mem.loadv. rewrite U. rewrite zle_true by exact BOUND. exact SINGLE.
Qed.

Theorem put32_reader_input : forall m b ofs x after,
  Ptrofs.unsigned ofs + 4 <= Ptrofs.modulus ->
  byte_writes m b (Ptrofs.unsigned ofs) (put32_values x) after ->
  reader_input after b ofs f_get32 (Vint x) 59.
Proof.
  intros m b ofs x after BOUND WRITES.
  pose proof (byte_writes_content _ _ _ _ _ WRITES ltac:(discriminate)) as LOAD.
  rewrite <- (put_get32_word x). apply input32; [assumption|].
  unfold loads32; repeat split.
  - pose proof (encoded_byte_load after b ofs [] (put32_byte x 0) [put32_byte x 1; put32_byte x 2; put32_byte x 3]
      ltac:(cbn [length]; lia) LOAD) as BYTE.
    unfold put32_byte in BYTE. rewrite Int.zero_ext_idem in BYTE by lia. exact BYTE.
  - pose proof (encoded_byte_load after b ofs [put32_byte x 0] (put32_byte x 1) [put32_byte x 2; put32_byte x 3]
      ltac:(cbn [length]; lia) LOAD) as BYTE.
    unfold put32_byte in BYTE. rewrite Int.zero_ext_idem in BYTE by lia. exact BYTE.
  - pose proof (encoded_byte_load after b ofs [put32_byte x 0; put32_byte x 1] (put32_byte x 2) [put32_byte x 3]
      ltac:(cbn [length]; lia) LOAD) as BYTE.
    unfold put32_byte in BYTE. rewrite Int.zero_ext_idem in BYTE by lia. exact BYTE.
  - pose proof (encoded_byte_load after b ofs [put32_byte x 0; put32_byte x 1; put32_byte x 2] (put32_byte x 3) []
      ltac:(cbn [length]; lia) LOAD) as BYTE.
    unfold put32_byte in BYTE. rewrite Int.zero_ext_idem in BYTE by lia. exact BYTE.
Qed.

Theorem put32_source_roundtrip : forall cell m b ofs x events after,
  writer_input m b ofs f_put32 (Vint x) (put32_values x) 42 ->
  steps (Clight.globalenv Slice.prog) cell
    (live (writer_initial f_put32 b ofs (Vint x) Kstop m)) events
    (live (Returnstate Vundef Kstop after)) ->
  steps (Clight.globalenv Slice.prog) cell (live (Readers.initial f_get32 b ofs Kstop after))
    (repeat (source_step E0) 59) (live (Returnstate (Vint x) Kstop after)) /\
  (forall reader_events actual final,
    steps (Clight.globalenv Slice.prog) cell (live (Readers.initial f_get32 b ofs Kstop after))
      reader_events (live (Returnstate actual Kstop final)) ->
    actual = Vint x /\ final = after /\ reader_events = repeat (source_step E0) 59).
Proof.
  intros cell m b ofs x events after INPUT RUN.
  destruct (writer_return_exact _ _ _ _ _ _ _ _ _ _ _ INPUT RUN) as [_ [_ [WRITES _]]].
  assert (BOUND : Ptrofs.unsigned ofs + 4 <= Ptrofs.modulus) by (inversion INPUT; assumption).
  pose proof (put32_reader_input _ _ _ _ _ BOUND WRITES) as READ.
  split; [apply reader_success_exists; exact READ|].
  intros; eapply reader_return_exact; eassumption.
Qed.

Theorem put64_reader_input : forall m b ofs x after,
  Ptrofs.unsigned ofs + 8 <= Ptrofs.modulus ->
  byte_writes m b (Ptrofs.unsigned ofs) (put64_values x) after ->
  reader_input after b ofs f_get64 (Vlong x) 103.
Proof.
  intros m b ofs x after BOUND WRITES.
  pose proof (byte_writes_content _ _ _ _ _ WRITES ltac:(discriminate)) as LOAD.
  rewrite <- (put_get64_word x). apply input64; [assumption|].
  unfold loads64, loads32; repeat split.
  - pose proof (encoded_byte_load after b ofs [] (put64_byte x 0) [put64_byte x 1; put64_byte x 2; put64_byte x 3; put64_byte x 4; put64_byte x 5; put64_byte x 6; put64_byte x 7]
      ltac:(cbn [length]; lia) LOAD) as BYTE.
    unfold put64_byte in BYTE. rewrite Int.zero_ext_idem in BYTE by lia. exact BYTE.
  - pose proof (encoded_byte_load after b ofs [put64_byte x 0] (put64_byte x 1) [put64_byte x 2; put64_byte x 3; put64_byte x 4; put64_byte x 5; put64_byte x 6; put64_byte x 7]
      ltac:(cbn [length]; lia) LOAD) as BYTE.
    unfold put64_byte in BYTE. rewrite Int.zero_ext_idem in BYTE by lia. exact BYTE.
  - pose proof (encoded_byte_load after b ofs [put64_byte x 0; put64_byte x 1] (put64_byte x 2) [put64_byte x 3; put64_byte x 4; put64_byte x 5; put64_byte x 6; put64_byte x 7]
      ltac:(cbn [length]; lia) LOAD) as BYTE.
    unfold put64_byte in BYTE. rewrite Int.zero_ext_idem in BYTE by lia. exact BYTE.
  - pose proof (encoded_byte_load after b ofs [put64_byte x 0; put64_byte x 1; put64_byte x 2] (put64_byte x 3) [put64_byte x 4; put64_byte x 5; put64_byte x 6; put64_byte x 7]
      ltac:(cbn [length]; lia) LOAD) as BYTE.
    unfold put64_byte in BYTE. rewrite Int.zero_ext_idem in BYTE by lia. exact BYTE.
  - pose proof (encoded_byte_load after b ofs [put64_byte x 0; put64_byte x 1; put64_byte x 2; put64_byte x 3] (put64_byte x 4) [put64_byte x 5; put64_byte x 6; put64_byte x 7]
      ltac:(cbn [length]; lia) LOAD) as BYTE.
    unfold put64_byte in BYTE. rewrite Int.zero_ext_idem in BYTE by lia. exact BYTE.
  - pose proof (encoded_byte_load after b ofs [put64_byte x 0; put64_byte x 1; put64_byte x 2; put64_byte x 3; put64_byte x 4] (put64_byte x 5) [put64_byte x 6; put64_byte x 7]
      ltac:(cbn [length]; lia) LOAD) as BYTE.
    unfold put64_byte in BYTE. rewrite Int.zero_ext_idem in BYTE by lia. exact BYTE.
  - pose proof (encoded_byte_load after b ofs [put64_byte x 0; put64_byte x 1; put64_byte x 2; put64_byte x 3; put64_byte x 4; put64_byte x 5] (put64_byte x 6) [put64_byte x 7]
      ltac:(cbn [length]; lia) LOAD) as BYTE.
    unfold put64_byte in BYTE. rewrite Int.zero_ext_idem in BYTE by lia. exact BYTE.
  - pose proof (encoded_byte_load after b ofs [put64_byte x 0; put64_byte x 1; put64_byte x 2; put64_byte x 3; put64_byte x 4; put64_byte x 5; put64_byte x 6] (put64_byte x 7) []
      ltac:(cbn [length]; lia) LOAD) as BYTE.
    unfold put64_byte in BYTE. rewrite Int.zero_ext_idem in BYTE by lia. exact BYTE.
Qed.

Theorem put64_source_roundtrip : forall cell m b ofs x events after,
  writer_input m b ofs f_put64 (Vlong x) (put64_values x) 74 ->
  steps (Clight.globalenv Slice.prog) cell
    (live (writer_initial f_put64 b ofs (Vlong x) Kstop m)) events
    (live (Returnstate Vundef Kstop after)) ->
  steps (Clight.globalenv Slice.prog) cell (live (Readers.initial f_get64 b ofs Kstop after))
    (repeat (source_step E0) 103) (live (Returnstate (Vlong x) Kstop after)) /\
  (forall reader_events actual final,
    steps (Clight.globalenv Slice.prog) cell (live (Readers.initial f_get64 b ofs Kstop after))
      reader_events (live (Returnstate actual Kstop final)) ->
    actual = Vlong x /\ final = after /\ reader_events = repeat (source_step E0) 103).
Proof.
  intros cell m b ofs x events after INPUT RUN.
  destruct (writer_return_exact _ _ _ _ _ _ _ _ _ _ _ INPUT RUN) as [_ [_ [WRITES _]]].
  assert (BOUND : Ptrofs.unsigned ofs + 8 <= Ptrofs.modulus) by (inversion INPUT; assumption).
  pose proof (put64_reader_input _ _ _ _ _ BOUND WRITES) as READ.
  split; [apply reader_success_exists; exact READ|].
  intros; eapply reader_return_exact; eassumption.
Qed.
