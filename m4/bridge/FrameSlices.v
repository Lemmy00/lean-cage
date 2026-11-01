(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-bridge.frames: Exact imported frame operations and source observations. *)
From Stdlib Require Import Arith List Lia.
From LeanImport Require Import Lean.
From compcert Require Import Integers.
Require Import NormalizedImport BridgeNat BridgeBytes FrameLists FrameArray FrameAppend.
Local Close Scope lean_scope.
Local Open Scope nat_scope.
Import ListNotations.

Definition bytes_list (b : ByteArray) := array_values (ByteArray_data b).
Lemma bytes_list_injective (a b : ByteArray) : bytes_list a = bytes_list b -> a = b.
Proof. destruct a as [a], b as [b]; intro H; apply f_equal; now apply array_values_injective. Qed.
Lemma byte_copy_slice_exact src srcOff dest destOff len exact :
 bytes_list (ByteArray_copySlice src srcOff dest destOff len exact) =
 firstn (nat_of_Nat destOff) (bytes_list dest) ++
 firstn (nat_of_Nat len) (skipn (nat_of_Nat srcOff) (bytes_list src)) ++
 skipn (nat_of_Nat destOff + Nat.min (nat_of_Nat len) (length (bytes_list src) - nat_of_Nat srcOff)) (bytes_list dest).
Proof.
 unfold ByteArray_copySlice, bytes_list.
 change (array_values (Array_append_inst1 UInt8
   (Array_append_inst1 UInt8
     (Array_extract_inst1 UInt8 (ByteArray_data dest) Nat_zero destOff)
     (Array_extract_inst1 UInt8 (ByteArray_data src) srcOff (Nat_add srcOff len)))
   (Array_extract_inst1 UInt8 (ByteArray_data dest)
     (Nat_add destOff (Min_min_inst1 Nat instMinNat len (Nat_sub (Array_size_inst1 UInt8 (ByteArray_data src)) srcOff)))
     (Array_size_inst1 UInt8 (ByteArray_data dest)))) =
   firstn (nat_of_Nat destOff) (array_values (ByteArray_data dest)) ++
   firstn (nat_of_Nat len) (skipn (nat_of_Nat srcOff) (array_values (ByteArray_data src))) ++
   skipn (nat_of_Nat destOff + Nat.min (nat_of_Nat len) (length (array_values (ByteArray_data src)) - nat_of_Nat srcOff))
     (array_values (ByteArray_data dest))).
 rewrite !(array_append_exact _ _ _ (imported_byte Byte.zero)).
 rewrite !(array_extract_exact _ _ _ _ (imported_byte Byte.zero)).
 rewrite !imported_add_exact, !imported_min_exact, !imported_sub_exact, !array_size_exact.
 cbn [nat_of_Nat skipn]; rewrite Nat.sub_0_r, Nat.add_sub_swap by lia.
 rewrite Nat.sub_diag, Nat.add_0_l.
 rewrite <- length_skipn, firstn_all, app_assoc; reflexivity.
Qed.
Lemma byte_extract_exact bytes start stop :
 bytes_list (ByteArray_extract bytes start stop) =
 firstn (nat_of_Nat stop - nat_of_Nat start) (skipn (nat_of_Nat start) (bytes_list bytes)).
Proof.
 unfold ByteArray_extract; rewrite byte_copy_slice_exact.
 cbn [bytes_list ByteArray_empty array_values Array_toList_inst1 ByteArray_data standard_list nat_of_Nat firstn app].
 rewrite skipn_nil, app_nil_r, imported_sub_exact; reflexivity.
Qed.
Lemma imported_bytes_list bs : bytes_list (imported_bytes bs) = List.map imported_byte bs.
Proof. apply standard_imported_list. Qed.
Theorem imported_extract_exact bs start stop :
 ByteArray_extract (imported_bytes bs) (Nat_of_nat start) (Nat_of_nat stop) =
 imported_bytes (firstn (stop-start) (skipn start bs)).
Proof.
 apply bytes_list_injective; rewrite byte_extract_exact, !imported_bytes_list, !nat2Natid.
 rewrite skipn_map, firstn_map; reflexivity.
Qed.
Theorem imported_size_exact bs : nat_of_Nat (ByteArray_size (imported_bytes bs)) = length bs.
Proof. change (nat_of_Nat (Array_size_inst1 UInt8 (ByteArray_data (imported_bytes bs))) = length bs).
 rewrite array_size_exact; change (length (bytes_list (imported_bytes bs)) = length bs).
 rewrite imported_bytes_list, length_map; reflexivity.
Qed.
