(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-bridge.frames: Exact imported frame operations and source observations. *)
From Stdlib Require Import ZArith List Lia Bool.
From LeanImport Require Import Lean.
From compcert Require Import Integers.
Require Import NormalizedImport BridgeNat BridgeBytes FrameLists FrameArray
 FrameSlices FrameEquality.
Local Close Scope lean_scope.
Local Open Scope nat_scope.
Import ListNotations.

Theorem byte_equality_exact a b : standard_bool (ByteArray_beq a b) = true <-> a = b.
Proof.
 change (standard_bool (Array_isEqv_inst1 UInt8 (ByteArray_data a) (ByteArray_data b)
   (fun x y => Decidable_decide (Lean.eq x y) (instDecidableEqUInt8 x y))) = true <-> a = b).
 rewrite (array_eq_exact _ _ _ _ (decide_equality_exact UInt8 instDecidableEqUInt8) (imported_byte Byte.zero)).
 change (bytes_list a = bytes_list b <-> a = b).
 split; [apply bytes_list_injective|intro E;now rewrite E].
Qed.
Lemma imported_byte_injective a b : imported_byte a = imported_byte b -> a = b.
Proof.
 intro E; apply (f_equal (fun x => nat_of_Nat (UInt8_toNat x))) in E.
 rewrite !imported_byte_exact in E.
 assert (U : Byte.unsigned a = Byte.unsigned b).
 { pose proof (Byte.unsigned_range a); pose proof (Byte.unsigned_range b); lia. }
 rewrite <- (Byte.repr_unsigned a), <- (Byte.repr_unsigned b); now rewrite U.
Qed.
Lemma imported_bytes_injective a b : imported_bytes a = imported_bytes b -> a = b.
Proof.
 intro E; apply (f_equal bytes_list) in E; rewrite !imported_bytes_list in E.
 revert b E; induction a as [|a xs IH]; intros [|b ys] E; cbn [List.map] in E; try discriminate; [reflexivity|].
 pose proof (f_equal (List.hd (imported_byte Byte.zero)) E) as HEAD.
 pose proof (f_equal (@List.tl UInt8) E) as TAIL.
 f_equal; [exact (imported_byte_injective a b HEAD)|exact (IH ys TAIL)].
Qed.
Theorem imported_bytes_equality_exact a b :
 standard_bool (ByteArray_beq (imported_bytes a) (imported_bytes b)) = true <-> a = b.
Proof.
 rewrite byte_equality_exact; split; [apply imported_bytes_injective|intro E;now rewrite E].
Qed.
