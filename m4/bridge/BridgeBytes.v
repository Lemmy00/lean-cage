(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-bridge.bytes: Explicit imported values connected to actual source executions. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Zbits Integers.
From LeanImport Require Import Lean.
Require Import NormalizedImport BridgeNat.
Local Close Scope lean_scope.
Local Open Scope Z_scope.

Definition imported_byte (b : Byte.int) : UInt8.
Proof.
 refine (UInt8_ofBitVec (BitVec_ofFin _ (Fin_mk _ (Nat_of_nat (Z.to_nat (Byte.unsigned b))) _))).
 change (Nat_le (Nat_of_nat (S (Z.to_nat (Byte.unsigned b)))) (Nat_of_nat 256)).
 apply nat_le_Nat_le.
 pose proof (Byte.unsigned_range b).
 change (0 <= Byte.unsigned b < 256) in H.
 rewrite !nat2Natid; lia.
Defined.
Lemma imported_byte_exact b :
 nat_of_Nat (UInt8_toNat (imported_byte b)) = Z.to_nat (Byte.unsigned b).
Proof. apply nat2Natid. Qed.
Definition imported_bytes (bs : list Byte.int) : ByteArray :=
 ByteArray_mk (Array_mk_inst1 UInt8 (imported_list (List.map imported_byte bs))).
Lemma imported_bytes_exact bs :
 byte_values (imported_bytes bs) = List.map (fun b => Z.to_nat (Byte.unsigned b)) bs.
Proof.
 unfold byte_values, imported_bytes.
 change (List.map (fun b : UInt8 => nat_of_Nat (UInt8_toNat b))
   (standard_list (imported_list (List.map imported_byte bs))) =
   List.map (fun b => Z.to_nat (Byte.unsigned b)) bs).
 rewrite standard_imported_list, List.map_map.
 apply List.map_ext; apply imported_byte_exact.
Qed.
Theorem imported_little_bytes_exact bs offset width :
 nat_of_Nat (LeanCageM4_Normalized_littleBytes (imported_bytes bs)
   (Nat_of_nat offset) (Nat_of_nat width)) =
 natural_little (List.map (fun b => Z.to_nat (Byte.unsigned b)) bs) offset width.
Proof. rewrite imported_little_exact, imported_bytes_exact, !nat2Natid; reflexivity. Qed.

Lemma separated_lor lo hi bits :
 0 <= bits -> 0 <= lo < two_p bits ->
 Z.lor lo (Z.shiftl hi bits) = lo + hi * two_p bits.
Proof.
 intros BITS LOW.
 assert (DISJOINT : Z.land lo (Z.shiftl hi bits) = 0).
 { apply Z.bits_inj; intro i. rewrite Z.land_spec, Z.bits_0.
   destruct (zlt i bits).
   - rewrite Z.shiftl_spec_low by lia; apply Bool.andb_false_r.
   - rewrite (Ztestbit_above (Z.to_nat bits) lo i).
     + reflexivity.
     + rewrite two_power_nat_two_p, Z2Nat.id by lia; exact LOW.
     + rewrite Z2Nat.id by lia; lia. }
 rewrite <- Z.lxor_lor by exact DISJOINT.
 rewrite <- Z.add_nocarry_lxor by exact DISJOINT.
 rewrite Zshiftl_mul_two_p by assumption; reflexivity.
Qed.
