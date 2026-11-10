(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Absolute-path checks inspect the real initialized signed C character. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata.
Require Import Readers.
From HostGateway Require Import GatewayErrorRuntime GatewayWordsMemory GatewayWordReceipt.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Theorem gateway_bootstrap_first_character memory object offset bytes :
  gateway_error_cstring memory (Vptr object offset) bytes ->
  Mem.loadv Mint8signed memory (Vptr object offset) =
    Some (Vint (Int.sign_ext 8 (Readers.byte_word (hd Byte.zero bytes)))).
Proof.
  intros [actual [actual_offset [POINTER [NONZERO [BOUND LOAD]]]]].
  inversion POINTER; subst actual actual_offset.
  assert (SIZE : Ptrofs.unsigned offset + Z.of_nat (length (bytes ++ [Byte.zero])) <= Ptrofs.modulus).
  { rewrite length_app, Nat2Z.inj_add; cbn; lia. }
  assert (LOADED : Mem.loadbytes memory object (Ptrofs.unsigned offset)
    (Z.of_nat (length (bytes ++ [Byte.zero]))) = Some (map Byte (bytes ++ [Byte.zero]))).
  { rewrite length_app, Nat2Z.inj_add; cbn; exact LOAD. }
  pose proof (gateway_read_ready_from_bytes memory object offset (bytes ++ [Byte.zero]) SIZE LOADED) as READY.
  assert (FIRST : nth_error (map Readers.byte_word (bytes ++ [Byte.zero])) 0 =
    Some (Readers.byte_word (hd Byte.zero bytes))) by (destruct bytes; reflexivity).
  specialize (READY 0%nat _ FIRST).
  change (Mem.loadv Mint8unsigned memory (Vptr object (Ptrofs.add offset Ptrofs.zero)) =
    Some (Vint (Readers.byte_word (hd Byte.zero bytes)))) in READY.
  rewrite Ptrofs.add_zero in READY.
  unfold Mem.loadv in READY |- *; destruct (zle _ _); [|discriminate].
  rewrite Mem.load_int8_signed_unsigned, READY; reflexivity.
Qed.

Theorem gateway_bootstrap_signed_slash byte :
  Int.sign_ext 8 (Readers.byte_word byte) = Int.repr 47 <-> byte = Byte.repr 47.
Proof.
  split; [|intro SAME; subst byte; reflexivity].
  intro SAME.
  pose proof (Int.eqmod_sign_ext 8 (Readers.byte_word byte) ltac:(change (0 < 8 < 32); lia))
    as [quotient CONGRUENT].
  rewrite SAME in CONGRUENT.
  change (Int.signed (Int.repr 47)) with 47 in CONGRUENT.
  change (two_p 8) with 256 in CONGRUENT.
  unfold Readers.byte_word in CONGRUENT.
  pose proof (Byte.unsigned_range byte) as RANGE; change (0 <= Byte.unsigned byte < 256) in RANGE.
  rewrite Int.unsigned_repr in CONGRUENT by (change Int.max_unsigned with 4294967295; lia).
  assert (VALUE : Byte.unsigned byte = 47) by lia.
  rewrite <- (Byte.repr_unsigned byte), VALUE; reflexivity.
Qed.
