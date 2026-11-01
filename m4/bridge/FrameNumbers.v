(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-bridge.frames: Exact imported frame operations and source observations. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers.
From LeanImport Require Import Lean.
Require Import NormalizedImport BridgeNat BridgeBytes BridgeWords
 Readers FrameBytes FrameRecord DecoderValidity WireWords WireFields WireLayout.
Local Close Scope lean_scope.
Local Open Scope Z_scope.
Import ListNotations.

Definition imported_int32 x := Nat_of_nat (Z.to_nat (Int.unsigned x)).
Definition imported_int64 x := Nat_of_nat (Z.to_nat (Int64.unsigned x)).
Lemma imported_nat_injective a b : nat_of_Nat a = nat_of_Nat b -> a = b.
Proof. intro E; rewrite <- (Nat2natid a), <- (Nat2natid b); now rewrite E. Qed.
Theorem imported_little32_value bs offset :
 LeanCageM4_Normalized_littleBytes (imported_bytes bs) (Nat_of_nat offset) (Nat_of_nat 4) =
 imported_int32 (word32_at bs offset).
Proof.
 apply imported_nat_injective; unfold imported_int32; rewrite nat2Natid, imported_word32_unsigned, Nat2Z.id; reflexivity.
Qed.
Theorem imported_little64_value bs offset :
 LeanCageM4_Normalized_littleBytes (imported_bytes bs) (Nat_of_nat offset) (Nat_of_nat 8) =
 imported_int64 (word64_at bs offset).
Proof.
 apply imported_nat_injective; unfold imported_int64; rewrite nat2Natid, imported_word64_unsigned, Nat2Z.id; reflexivity.
Qed.
Lemma natural_little_two bytes offset :
 natural_little bytes offset 2 = (nth offset bytes 0 + nth (offset+1) bytes 0 * Nat.pow 2 8)%nat.
Proof.
 unfold natural_little; cbn [List.seq List.fold_left].
 rewrite Nat.add_0_r, Nat.mul_1_r; reflexivity.
Qed.
Theorem imported_little_two_numeric bs offset :
 Z.of_nat (nat_of_Nat (LeanCageM4_Normalized_littleBytes (imported_bytes bs)
   (Nat_of_nat offset) (Nat_of_nat 2))) =
 Byte.unsigned (nth offset bs Byte.zero) + Byte.unsigned (nth (offset+1)%nat bs Byte.zero)*256.
Proof.
 rewrite imported_little_bytes_exact, natural_little_two.
 rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul, !natural_byte_at_Z, !Nat2Z.inj_pow; reflexivity.
Qed.
Theorem imported_frame_version sequence r digest :
 LeanCageM4_Normalized_littleBytes (imported_bytes (outgoing_frame sequence r digest)) 4 2 = Nat_succ Nat_zero.
Proof.
 apply imported_nat_injective; apply Nat2Z.inj.
 change (Z.of_nat (nat_of_Nat (LeanCageM4_Normalized_littleBytes
   (imported_bytes (outgoing_frame sequence r digest)) (Nat_of_nat 4) (Nat_of_nat 2))) = 1).
 rewrite imported_little_two_numeric; reflexivity.
Qed.
Theorem imported_frame_kind sequence r digest :
 LeanCageM4_Normalized_littleBytes (imported_bytes (outgoing_frame sequence r digest)) 6 2 =
 imported_int32 (Int.zero_ext 8 (fr_kind r)).
Proof.
 apply imported_nat_injective; apply Nat2Z.inj.
 unfold imported_int32; rewrite nat2Natid, Z2Nat.id by (pose proof (Int.unsigned_range (Int.zero_ext 8 (fr_kind r))); lia).
 change (Z.of_nat (nat_of_Nat (LeanCageM4_Normalized_littleBytes
   (imported_bytes (outgoing_frame sequence r digest)) (Nat_of_nat 6) (Nat_of_nat 2))) =
   Int.unsigned (Int.zero_ext 8 (fr_kind r))).
 rewrite imported_little_two_numeric.
 unfold outgoing_frame,frame_magic; cbn [app nth].
 change (Byte.unsigned (Byte.repr (Int.unsigned (fr_kind r))) + 0*256 = Int.unsigned (Int.zero_ext 8 (fr_kind r))).
 rewrite <- (wire_byte_word (fr_kind r)), byte_word_unsigned; lia.
Qed.
Theorem imported_frame_terminal sequence r digest : length digest=32%nat ->
 LeanCageM4_Normalized_littleBytes (imported_bytes (outgoing_frame sequence r digest)) 156 4 = Nat_zero.
Proof.
 intro LEN; change (LeanCageM4_Normalized_littleBytes (imported_bytes (outgoing_frame sequence r digest))
   (Nat_of_nat 156) (Nat_of_nat 4) = Nat_zero).
 rewrite imported_little32_value, wire_word32_skip, wire_terminal_suffix by exact LEN; reflexivity.
Qed.
