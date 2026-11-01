(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-bridge.frames: Exact imported frame operations and source observations. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Integers.
From LeanImport Require Import Lean.
Require Import NormalizedImport BridgeNat BridgeBytes FrameLists FrameEquality
 FrameByteEq FrameParser FrameNumbers.
Local Close Scope lean_scope.
Local Open Scope Z_scope.
Import ListNotations.
Definition natural_value a := Z.of_nat (nat_of_Nat a).
Lemma imported_int32_number x : natural_value (imported_int32 x) = Int.unsigned x.
Proof. unfold natural_value,imported_int32; rewrite nat2Natid, Z2Nat.id; [reflexivity|pose proof (Int.unsigned_range x);lia]. Qed.
Lemma imported_int64_number x : natural_value (imported_int64 x) = Int64.unsigned x.
Proof. unfold natural_value,imported_int64; rewrite nat2Natid, Z2Nat.id; [reflexivity|pose proof (Int64.unsigned_range x);lia]. Qed.
Lemma standard_bool_or a b : standard_bool (Bool_or a b) = orb (standard_bool a) (standard_bool b).
Proof. destruct a,b; reflexivity. Qed.
Lemma imported_beq_number a b : standard_bool (Nat_beq a b) = Z.eqb (natural_value a) (natural_value b).
Proof. rewrite imported_beq_exact, ZifyBool.Z_of_nat_eqb_iff; reflexivity. Qed.
Lemma imported_ble_number a b : standard_bool (Nat_ble a b) = Z.leb (natural_value a) (natural_value b).
Proof. rewrite imported_ble_exact, ZifyBool.Z_of_nat_leb_iff; reflexivity. Qed.
Lemma imported_decLt_number a b : standard_bool (Decidable_decide (Nat_le (Nat_succ a) b) (Nat_decLt a b)) =
 Z.ltb (natural_value a) (natural_value b).
Proof.
 change (standard_bool (Nat_ble (Nat_succ a) b) = Z.ltb (natural_value a) (natural_value b)).
 rewrite imported_ble_exact.
 change (Nat.ltb (nat_of_Nat a) (nat_of_Nat b) = Z.ltb (natural_value a) (natural_value b)).
 rewrite ZifyBool.Z_of_nat_ltb_iff; reflexivity.
Qed.
Lemma imported_ite_lt_number A a b (t e : A) :
 ite A (Nat_le (Nat_succ a) b) (Nat_decLt a b) t e =
 if Z.ltb (natural_value a) (natural_value b) then t else e.
Proof.
 unfold Nat_decLt; rewrite imported_ite_le.
 change ((if Nat.ltb (nat_of_Nat a) (nat_of_Nat b) then t else e) =
   if Z.ltb (natural_value a) (natural_value b) then t else e).
 rewrite ZifyBool.Z_of_nat_ltb_iff; reflexivity.
Qed.
Definition entry_equal a b := match a,b with
 | LeanCageM3_Entry_no, LeanCageM3_Entry_no
 | LeanCageM3_Entry_yes, LeanCageM3_Entry_yes
 | LeanCageM3_Entry_unknown, LeanCageM3_Entry_unknown => true
 | _,_ => false end.
Lemma imported_entry_equal a b :
 standard_bool (BEq_beq_inst1 LeanCageM3_Entry
  (instBEqOfDecidableEq_inst1 LeanCageM3_Entry LeanCageM3_instDecidableEqEntry) a b) = entry_equal a b.
Proof. destruct a,b; reflexivity. Qed.
Definition source_bytes_equal a b := if list_eq_dec Byte.eq_dec a b then true else false.
Lemma source_bytes_equal_true a b : source_bytes_equal a b = true <-> a=b.
Proof. unfold source_bytes_equal; destruct (list_eq_dec Byte.eq_dec a b); split; intros; congruence. Qed.
Lemma imported_byte_equality_bool a b :
 standard_bool (ByteArray_beq (imported_bytes a) (imported_bytes b)) = source_bytes_equal a b.
Proof. apply eq_true_iff_eq; rewrite imported_bytes_equality_exact, source_bytes_equal_true; reflexivity. Qed.
Lemma imported_zero_digest :
 ByteArray_mk (Array_replicate_inst1 UInt8 32 (OfNat_ofNat_inst1 UInt8 0 (UInt8_instOfNat 0))) =
 imported_bytes (repeat Byte.zero 32).
Proof. reflexivity. Qed.
Lemma validity_match_exact (A : Type) n (z o t th f s : A) (other : Nat -> A) :
 LeanCageM3_resultValid_match_1 (fun _ => A) n (fun _ => z) (fun _ => o) (fun _ => t)
   (fun _ => th) (fun _ => f) (fun _ => s) other =
 match n with
 | Nat_zero => z | Nat_succ Nat_zero => o | Nat_succ (Nat_succ Nat_zero) => t
 | Nat_succ (Nat_succ (Nat_succ Nat_zero)) => th
 | Nat_succ (Nat_succ (Nat_succ (Nat_succ Nat_zero))) => f
 | Nat_succ (Nat_succ (Nat_succ (Nat_succ (Nat_succ (Nat_succ (Nat_succ Nat_zero)))))) => s
 | _ => other n end.
Proof. destruct n as [|[|[|[|[|[|[|[|n]]]]]]]]; reflexivity. Qed.
Lemma imported_decLe_number a b :
 standard_bool (Decidable_decide (Nat_le a b) (Nat_decLe a b)) = Z.leb (natural_value a) (natural_value b).
Proof. apply imported_ble_number. Qed.
Lemma standard_bool_if (b : bool) (t e : Bool) :
 standard_bool (if b then t else e) = if b then standard_bool t else standard_bool e.
Proof. destruct b; reflexivity. Qed.
Lemma standard_bool_kind_match n (z o t th f s : Bool) :
 standard_bool (match n with
 | Nat_zero => z | Nat_succ Nat_zero => o | Nat_succ (Nat_succ Nat_zero) => t
 | Nat_succ (Nat_succ (Nat_succ Nat_zero)) => th
 | Nat_succ (Nat_succ (Nat_succ (Nat_succ Nat_zero))) => f
 | Nat_succ (Nat_succ (Nat_succ (Nat_succ (Nat_succ (Nat_succ (Nat_succ Nat_zero)))))) => s
 | _ => Bool_false end) =
 match nat_of_Nat n with
 | 0%nat => standard_bool z | 1%nat => standard_bool o | 2%nat => standard_bool t
 | 3%nat => standard_bool th | 4%nat => standard_bool f | 7%nat => standard_bool s | _ => false end.
Proof. destruct n as [|[|[|[|[|[|[|[|n]]]]]]]]; reflexivity. Qed.
Lemma imported_nat_number n : natural_value (Nat_of_nat n) = Z.of_nat n.
Proof. unfold natural_value; now rewrite nat2Natid. Qed.
