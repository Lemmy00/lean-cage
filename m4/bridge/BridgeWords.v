(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-bridge.bytes: Explicit imported values connected to actual source executions. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Zbits Integers.
From LeanImport Require Import Lean.
Require Import NormalizedImport BridgeNat Codec Readers FrameBytes BridgeBytes.
Local Close Scope lean_scope.
Local Open Scope Z_scope.

Lemma int32_low_shifted lo hi bits :
 0 <= bits <= 24 -> 0 <= lo < two_p bits -> 0 <= hi < 256 ->
 Int.or (Int.repr lo) (Int.shl (Int.repr hi) (Int.repr bits)) =
 Int.repr (lo + hi * two_p bits).
Proof.
 intros BITS LOW HIGH.
 assert (POW : 0 < two_p bits <= 16777216).
 { split; [pose proof (two_p_gt_ZERO bits ltac:(lia)); lia|].
   change (two_p bits <= two_p 24); apply two_p_monotone; lia. }
 unfold Int.or, Int.shl.
 rewrite (Int.unsigned_repr lo) by (change (0 <= lo <= 4294967295); lia).
 rewrite (Int.unsigned_repr hi) by (change (0 <= hi <= 4294967295); lia).
 rewrite (Int.unsigned_repr bits) by (change (0 <= bits <= 4294967295); lia).
 rewrite Zshiftl_mul_two_p by lia.
 rewrite Int.unsigned_repr by (change (0 <= hi * two_p bits <= 4294967295); nia).
 f_equal.
 rewrite <- (Zshiftl_mul_two_p hi bits) at 1 by lia.
 apply separated_lor; lia.
Qed.
Lemma byte_word_unsigned b : Int.unsigned (byte_word b) = Byte.unsigned b.
Proof.
 unfold byte_word; rewrite Int.unsigned_repr; [reflexivity|].
 pose proof (Byte.unsigned_range b); change (0 <= Byte.unsigned b < 256) in H.
 change (0 <= Byte.unsigned b <= 4294967295); lia.
Qed.
Theorem get32_bytes_numeric a b c d :
 get32_word (byte_word a) (byte_word b) (byte_word c) (byte_word d) =
 Int.repr (Byte.unsigned a + Byte.unsigned b*256 +
   Byte.unsigned c*65536 + Byte.unsigned d*16777216).
Proof.
 pose proof (Byte.unsigned_range a) as A; change (0 <= Byte.unsigned a < 256) in A.
 pose proof (Byte.unsigned_range b) as B; change (0 <= Byte.unsigned b < 256) in B.
 pose proof (Byte.unsigned_range c) as C; change (0 <= Byte.unsigned c < 256) in C.
 pose proof (Byte.unsigned_range d) as D; change (0 <= Byte.unsigned d < 256) in D.
 unfold get32_word.
 rewrite Int.or_zero_l, Int.shl_zero.
 unfold byte_word.
 rewrite int32_low_shifted by (try change (0 <= Byte.unsigned a < 256); lia).
 change (two_p 8) with 256.
 rewrite int32_low_shifted by (try change (0 <= Byte.unsigned a + Byte.unsigned b*256 < 65536); lia).
 change (two_p 16) with 65536.
 rewrite int32_low_shifted by (try change (0 <= Byte.unsigned a + Byte.unsigned b*256 + Byte.unsigned c*65536 < 16777216); lia).
 reflexivity.
Qed.

Lemma natural_little_four bytes offset :
 natural_little bytes offset 4 =
 (nth offset bytes 0 + nth (offset+1) bytes 0 * Nat.pow 2 8 +
  nth (offset+2) bytes 0 * Nat.pow 2 16 + nth (offset+3) bytes 0 * Nat.pow 2 24)%nat.
Proof.
 unfold natural_little; cbn [List.seq List.fold_left].
 rewrite Nat.add_0_r, Nat.mul_1_r; reflexivity.
Qed.
Lemma natural_byte_at bs n :
 nth n (List.map (fun b => Z.to_nat (Byte.unsigned b)) bs) 0%nat =
 Z.to_nat (Byte.unsigned (nth n bs Byte.zero)).
Proof.
 exact (@List.map_nth Byte.int nat (fun b => Z.to_nat (Byte.unsigned b)) bs Byte.zero n).
Qed.
Lemma natural_byte_at_Z bs n :
 Z.of_nat (nth n (List.map (fun b => Z.to_nat (Byte.unsigned b)) bs) 0%nat) =
 Byte.unsigned (nth n bs Byte.zero).
Proof.
 rewrite natural_byte_at, Z2Nat.id; [reflexivity|].
 pose proof (Byte.unsigned_range (nth n bs Byte.zero)); lia.
Qed.
Theorem imported_word32_exact bs offset :
 word32_at bs offset =
 Int.repr (Z.of_nat (nat_of_Nat
   (LeanCageM4_Normalized_littleBytes (imported_bytes bs) (Nat_of_nat offset) (Nat_of_nat 4)))).
Proof.
 rewrite imported_little_bytes_exact, natural_little_four.
 unfold word32_at, byte_word_at, byte_at; rewrite get32_bytes_numeric.
 rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul, !natural_byte_at_Z, !Nat2Z.inj_pow.
 reflexivity.
Qed.

Lemma int64_low_shifted lo hi bits :
 0 <= bits <= 56 -> 0 <= lo < two_p bits -> 0 <= hi < 256 ->
 Int64.or (Int64.repr lo) (Int64.shl (Int64.repr hi) (Int64.repr bits)) =
 Int64.repr (lo + hi * two_p bits).
Proof.
 intros BITS LOW HIGH.
 assert (POW : 0 < two_p bits <= 72057594037927936).
 { split; [pose proof (two_p_gt_ZERO bits ltac:(lia)); lia|].
   change (two_p bits <= two_p 56); apply two_p_monotone; lia. }
 unfold Int64.or, Int64.shl.
 rewrite (Int64.unsigned_repr lo) by (change (0 <= lo <= 18446744073709551615); lia).
 rewrite (Int64.unsigned_repr hi) by (change (0 <= hi <= 18446744073709551615); lia).
 rewrite (Int64.unsigned_repr bits) by (change (0 <= bits <= 18446744073709551615); lia).
 rewrite Zshiftl_mul_two_p by lia.
 rewrite Int64.unsigned_repr by (change (0 <= hi * two_p bits <= 18446744073709551615); nia).
 f_equal.
 rewrite <- (Zshiftl_mul_two_p hi bits) at 1 by lia.
 apply separated_lor; lia.
Qed.
Theorem get64_bytes_numeric a b c d e f g h :
 get64_word (byte_word a) (byte_word b) (byte_word c) (byte_word d) (byte_word e) (byte_word f) (byte_word g) (byte_word h) =
 Int64.repr (Byte.unsigned a + Byte.unsigned b*256 + Byte.unsigned c*65536 + Byte.unsigned d*16777216 + Byte.unsigned e*4294967296 + Byte.unsigned f*1099511627776 + Byte.unsigned g*281474976710656 + Byte.unsigned h*72057594037927936).
Proof.
 pose proof (Byte.unsigned_range a) as A; change (0 <= Byte.unsigned a < 256) in A.
 pose proof (Byte.unsigned_range b) as B; change (0 <= Byte.unsigned b < 256) in B.
 pose proof (Byte.unsigned_range c) as C; change (0 <= Byte.unsigned c < 256) in C.
 pose proof (Byte.unsigned_range d) as D; change (0 <= Byte.unsigned d < 256) in D.
 pose proof (Byte.unsigned_range e) as E; change (0 <= Byte.unsigned e < 256) in E.
 pose proof (Byte.unsigned_range f) as F; change (0 <= Byte.unsigned f < 256) in F.
 pose proof (Byte.unsigned_range g) as G; change (0 <= Byte.unsigned g < 256) in G.
 pose proof (Byte.unsigned_range h) as H; change (0 <= Byte.unsigned h < 256) in H.
 unfold get64_word; rewrite !byte_word_unsigned.
 rewrite Int64.or_zero_l, Int64.shl_zero.
 rewrite int64_low_shifted by (try change (0 <= Byte.unsigned a < 256); lia).
 change (two_p 8) with 256.
 rewrite int64_low_shifted by (try change (0 <= Byte.unsigned a + Byte.unsigned b*256 < 65536); lia).
 change (two_p 16) with 65536.
 rewrite int64_low_shifted by (try change (0 <= Byte.unsigned a + Byte.unsigned b*256 + Byte.unsigned c*65536 < 16777216); lia).
 change (two_p 24) with 16777216.
 rewrite int64_low_shifted by (try change (0 <= Byte.unsigned a + Byte.unsigned b*256 + Byte.unsigned c*65536 + Byte.unsigned d*16777216 < 4294967296); lia).
 change (two_p 32) with 4294967296.
 rewrite int64_low_shifted by (try change (0 <= Byte.unsigned a + Byte.unsigned b*256 + Byte.unsigned c*65536 + Byte.unsigned d*16777216 + Byte.unsigned e*4294967296 < 1099511627776); lia).
 change (two_p 40) with 1099511627776.
 rewrite int64_low_shifted by (try change (0 <= Byte.unsigned a + Byte.unsigned b*256 + Byte.unsigned c*65536 + Byte.unsigned d*16777216 + Byte.unsigned e*4294967296 + Byte.unsigned f*1099511627776 < 281474976710656); lia).
 change (two_p 48) with 281474976710656.
 rewrite int64_low_shifted by (try change (0 <= Byte.unsigned a + Byte.unsigned b*256 + Byte.unsigned c*65536 + Byte.unsigned d*16777216 + Byte.unsigned e*4294967296 + Byte.unsigned f*1099511627776 + Byte.unsigned g*281474976710656 < 72057594037927936); lia).
 reflexivity.
Qed.

Lemma natural_little_eight bytes offset :
 natural_little bytes offset 8 =
 (nth offset bytes 0 + nth (offset+1) bytes 0 * Nat.pow 2 8 + nth (offset+2) bytes 0 * Nat.pow 2 16 + nth (offset+3) bytes 0 * Nat.pow 2 24 + nth (offset+4) bytes 0 * Nat.pow 2 32 + nth (offset+5) bytes 0 * Nat.pow 2 40 + nth (offset+6) bytes 0 * Nat.pow 2 48 + nth (offset+7) bytes 0 * Nat.pow 2 56)%nat.
Proof.
 unfold natural_little; cbn [List.seq List.fold_left].
 rewrite Nat.add_0_r, Nat.mul_1_r; reflexivity.
Qed.
Theorem imported_word64_exact bs offset :
 word64_at bs offset =
 Int64.repr (Z.of_nat (nat_of_Nat
   (LeanCageM4_Normalized_littleBytes (imported_bytes bs) (Nat_of_nat offset) (Nat_of_nat 8)))).
Proof.
 rewrite imported_little_bytes_exact, natural_little_eight.
 unfold word64_at, byte_word_at, byte_at; rewrite get64_bytes_numeric.
 rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul, !natural_byte_at_Z, !Nat2Z.inj_pow.
 reflexivity.
Qed.

Theorem imported_little32_bounded bs offset :
 0 <= Z.of_nat (nat_of_Nat (LeanCageM4_Normalized_littleBytes (imported_bytes bs)
   (Nat_of_nat offset) (Nat_of_nat 4))) < Int.modulus.
Proof.
 rewrite imported_little_bytes_exact, natural_little_four.
 rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul, !natural_byte_at_Z, !Nat2Z.inj_pow.
 pose proof (Byte.unsigned_range (nth offset bs Byte.zero)) as B0.
 change (0 <= Byte.unsigned (nth offset bs Byte.zero) < 256) in B0.
 pose proof (Byte.unsigned_range (nth (offset+1)%nat bs Byte.zero)) as B1.
 change (0 <= Byte.unsigned (nth (offset+1)%nat bs Byte.zero) < 256) in B1.
 pose proof (Byte.unsigned_range (nth (offset+2)%nat bs Byte.zero)) as B2.
 change (0 <= Byte.unsigned (nth (offset+2)%nat bs Byte.zero) < 256) in B2.
 pose proof (Byte.unsigned_range (nth (offset+3)%nat bs Byte.zero)) as B3.
 change (0 <= Byte.unsigned (nth (offset+3)%nat bs Byte.zero) < 256) in B3.
 change Int.modulus with 4294967296.
 cbn [Z.of_nat Z.pow Z.pow_pos Pos.iter] ; lia.
Qed.
Theorem imported_word32_unsigned bs offset :
 Int.unsigned (word32_at bs offset) =
 Z.of_nat (nat_of_Nat (LeanCageM4_Normalized_littleBytes (imported_bytes bs)
   (Nat_of_nat offset) (Nat_of_nat 4))).
Proof.
 rewrite imported_word32_exact; apply Int.unsigned_repr.
 pose proof (imported_little32_bounded bs offset).
 unfold Int.max_unsigned; lia.
Qed.

Theorem imported_little64_bounded bs offset :
 0 <= Z.of_nat (nat_of_Nat (LeanCageM4_Normalized_littleBytes (imported_bytes bs)
   (Nat_of_nat offset) (Nat_of_nat 8))) < Int64.modulus.
Proof.
 rewrite imported_little_bytes_exact, natural_little_eight.
 rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul, !natural_byte_at_Z, !Nat2Z.inj_pow.
 pose proof (Byte.unsigned_range (nth offset bs Byte.zero)) as B0.
 change (0 <= Byte.unsigned (nth offset bs Byte.zero) < 256) in B0.
 pose proof (Byte.unsigned_range (nth (offset+1)%nat bs Byte.zero)) as B1.
 change (0 <= Byte.unsigned (nth (offset+1)%nat bs Byte.zero) < 256) in B1.
 pose proof (Byte.unsigned_range (nth (offset+2)%nat bs Byte.zero)) as B2.
 change (0 <= Byte.unsigned (nth (offset+2)%nat bs Byte.zero) < 256) in B2.
 pose proof (Byte.unsigned_range (nth (offset+3)%nat bs Byte.zero)) as B3.
 change (0 <= Byte.unsigned (nth (offset+3)%nat bs Byte.zero) < 256) in B3.
 pose proof (Byte.unsigned_range (nth (offset+4)%nat bs Byte.zero)) as B4.
 change (0 <= Byte.unsigned (nth (offset+4)%nat bs Byte.zero) < 256) in B4.
 pose proof (Byte.unsigned_range (nth (offset+5)%nat bs Byte.zero)) as B5.
 change (0 <= Byte.unsigned (nth (offset+5)%nat bs Byte.zero) < 256) in B5.
 pose proof (Byte.unsigned_range (nth (offset+6)%nat bs Byte.zero)) as B6.
 change (0 <= Byte.unsigned (nth (offset+6)%nat bs Byte.zero) < 256) in B6.
 pose proof (Byte.unsigned_range (nth (offset+7)%nat bs Byte.zero)) as B7.
 change (0 <= Byte.unsigned (nth (offset+7)%nat bs Byte.zero) < 256) in B7.
 change Int64.modulus with 18446744073709551616.
 cbn [Z.of_nat Z.pow Z.pow_pos Pos.iter] ; lia.
Qed.
Theorem imported_word64_unsigned bs offset :
 Int64.unsigned (word64_at bs offset) =
 Z.of_nat (nat_of_Nat (LeanCageM4_Normalized_littleBytes (imported_bytes bs)
   (Nat_of_nat offset) (Nat_of_nat 8))).
Proof.
 rewrite imported_word64_exact; apply Int64.unsigned_repr.
 pose proof (imported_little64_bounded bs offset).
 unfold Int64.max_unsigned; lia.
Qed.
