(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.encoding: Derive each writer and byte store from current local ownership. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Memdata Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Slice Machine ClightSteps WriteAll StoreSteps LocalAccess CallAccess Library Writers WriteBytes
  CallPaths FreshMemory ResultLayout FrameRecord SenderSource SenderAccess
  BytePatch SenderStorage.
Import ListNotations.
Open Scope Z_scope.

Theorem sender_writer32 : forall base m result_local bytes_local r digest bytes index x k,
  ~ Mem.valid_block base bytes_local -> result_local<>bytes_local ->
  sender_storage base result_local bytes_local r digest bytes m ->
  length bytes=160%nat -> (index+4<=160)%nat -> is_call_cont k ->
  exists after,
    store_path result_ge (old_memory base)
      (writer_initial f_put32 bytes_local (Ptrofs.repr (Z.of_nat index)) (Vint x) k m) 42
      (Returnstate Vundef k after) /\
    sender_storage base result_local bytes_local r digest
      (patch_bytes bytes index (frame_word32 x)) after.
Proof.
  intros base m result_local bytes_local r digest bytes index x k FRESH NE STORAGE LEN BOUND CALL.
  pose proof STORAGE as [OLD [OWN [READ [RFREE BFREE]]]].
  assert (U : Ptrofs.unsigned (Ptrofs.repr (Z.of_nat index))=Z.of_nat index)
    by (apply Ptrofs.unsigned_repr;change Ptrofs.max_unsigned with 18446744073709551615;lia).
  destruct (writer_caller_path result_ge m bytes_local (Ptrofs.repr (Z.of_nat index)) f_put32 (Vint x)
    (put32_values x) 42 k (old_memory base)) as [after [WRITES PATH]].
  - apply writer32_input;rewrite U.
    + change Ptrofs.modulus with 18446744073709551616;lia.
    + intros pos RANGE;eapply Mem.perm_implies;[apply BFREE;lia|constructor].
  - exact CALL.
  - intros after PREFIX;eapply fresh_writer_prefix_preserves_old;[exact FRESH|exact OLD|exact PREFIX].
  - exists after;split;[exact PATH|].
    unfold frame_word32;eapply sender_storage_writes;[exact FRESH|exact NE|exact STORAGE|rewrite LEN;exact BOUND|discriminate|].
    rewrite U in WRITES;exact WRITES.
Qed.

Theorem sender_writer64 : forall base m result_local bytes_local r digest bytes index x k,
  ~ Mem.valid_block base bytes_local -> result_local<>bytes_local ->
  sender_storage base result_local bytes_local r digest bytes m ->
  length bytes=160%nat -> (index+8<=160)%nat -> is_call_cont k ->
  exists after,
    store_path result_ge (old_memory base)
      (writer_initial f_put64 bytes_local (Ptrofs.repr (Z.of_nat index)) (Vlong x) k m) 74
      (Returnstate Vundef k after) /\
    sender_storage base result_local bytes_local r digest
      (patch_bytes bytes index (frame_word64 x)) after.
Proof.
  intros base m result_local bytes_local r digest bytes index x k FRESH NE STORAGE LEN BOUND CALL.
  pose proof STORAGE as [OLD [OWN [READ [RFREE BFREE]]]].
  assert (U : Ptrofs.unsigned (Ptrofs.repr (Z.of_nat index))=Z.of_nat index)
    by (apply Ptrofs.unsigned_repr;change Ptrofs.max_unsigned with 18446744073709551615;lia).
  destruct (writer_caller_path result_ge m bytes_local (Ptrofs.repr (Z.of_nat index)) f_put64 (Vlong x)
    (put64_values x) 74 k (old_memory base)) as [after [WRITES PATH]].
  - apply writer64_input;rewrite U.
    + change Ptrofs.modulus with 18446744073709551616;lia.
    + intros pos RANGE;eapply Mem.perm_implies;[apply BFREE;lia|constructor].
  - exact CALL.
  - intros after PREFIX;eapply fresh_writer_prefix_preserves_old;[exact FRESH|exact OLD|exact PREFIX].
  - exists after;split;[exact PATH|].
    unfold frame_word64;eapply sender_storage_writes;[exact FRESH|exact NE|exact STORAGE|rewrite LEN;exact BOUND|discriminate|].
    rewrite U in WRITES;exact WRITES.
Qed.

Theorem sender_byte_store : forall base m result_local bytes_local r digest bytes index x,
  ~ Mem.valid_block base bytes_local -> result_local<>bytes_local ->
  sender_storage base result_local bytes_local r digest bytes m ->
  length bytes=160%nat -> (index<160)%nat ->
  exists after,
    Mem.store Mint8unsigned m bytes_local (Z.of_nat index) (Vint x)=Some after /\
    sender_storage base result_local bytes_local r digest
      (patch_bytes bytes index [Byte.repr (Int.unsigned x)]) after.
Proof.
  intros base m result_local bytes_local r digest bytes index x FRESH NE STORAGE LEN BOUND.
  pose proof STORAGE as [OLD [OWN [READ [RFREE BFREE]]]].
  destruct (byte_writes_exists [x] m bytes_local (Z.of_nat index)) as [after WRITES].
  { intros pos RANGE;eapply Mem.perm_implies;[apply BFREE;cbn in RANGE;lia|constructor]. }
  inversion WRITES;subst;match goal with REST : byte_writes _ _ _ [] _ |- _ => inversion REST;subst end.
  exists after;split;[assumption|].
  change (sender_storage base result_local bytes_local r digest
    (patch_bytes bytes index (map (fun y=>Byte.repr (Int.unsigned y)) [x])) after).
  eapply sender_storage_writes;[exact FRESH|exact NE|exact STORAGE|rewrite LEN;cbn;lia|discriminate|exact WRITES].
Qed.

Lemma narrowed_byte : forall x,
  Byte.repr (Int.unsigned (Int.zero_ext 8 x))=Byte.repr (Int.unsigned x).
Proof.
  intros. rewrite Int.zero_ext_mod by (change Int.zwordsize with 32;lia).
  change (two_p 8) with Byte.modulus.
  rewrite <- Byte.unsigned_repr_eq. apply Byte.repr_unsigned.
Qed.
