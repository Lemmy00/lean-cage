(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-bridge.frames: Exact imported frame operations and source observations. *)
From Stdlib Require Import Arith List Lia Bool.
From LeanImport Require Import Lean.
Require Import NormalizedImport BridgeNat FrameLists FrameNumbers FrameMatch.
Local Close Scope lean_scope.
Local Open Scope nat_scope.
Local Opaque LeanCageM4_Normalized_fieldsBytes LeanCageM4_Normalized_littleBytes LeanCageM4_Normalized_headerBadBytes.

Lemma imported_ite_bool A b (t e : A) :
 ite A (Lean.eq b Bool_true) (instDecidableEqBool b Bool_true) t e =
 if standard_bool b then t else e.
Proof. destruct b; reflexivity. Qed.
Lemma imported_ite_le A a b (t e : A) :
 ite A (Nat_le a b) (Nat_decLe a b) t e =
 if Nat.leb (nat_of_Nat a) (nat_of_Nat b) then t else e.
Proof.
 destruct (le_dec (nat_of_Nat a) (nat_of_Nat b)) as [LE|GT].
 - rewrite (imported_ite_true _ _ _ _ _ (nat_le_Nat_le a b LE)).
   now rewrite (proj2 (Nat.leb_le _ _) LE).
 - pose proof (proj1 (Nat.nle_gt _ _) GT) as LT.
   rewrite (imported_ite_false _ _ _ _ _ (imported_not_le a b LT)).
   now rewrite (proj2 (Nat.leb_gt (nat_of_Nat a) (nat_of_Nat b)) LT).
Qed.
Definition parse_cleanup bytes entry :=
 if Nat.leb 2 (nat_of_Nat (LeanCageM4_Normalized_littleBytes bytes 44 4))
 then Except_error_inst3 LeanCageM4_Normalized_ErrorCode LeanCageM3_Result LeanCageM4_Normalized_ErrorCode_cleanup
 else Except_ok_inst3 LeanCageM4_Normalized_ErrorCode LeanCageM3_Result
   (LeanCageM4_Normalized_fieldsBytes bytes entry).
Definition parse_view bytes :=
 if standard_bool (LeanCageM4_Normalized_headerBadBytes bytes)
 then Except_error_inst3 LeanCageM4_Normalized_ErrorCode LeanCageM3_Result LeanCageM4_Normalized_ErrorCode_header
 else match nat_of_Nat (LeanCageM4_Normalized_littleBytes bytes 40 4) with
 | 0 => parse_cleanup bytes LeanCageM3_Entry_no
 | 1 => parse_cleanup bytes LeanCageM3_Entry_yes
 | 2 => parse_cleanup bytes LeanCageM3_Entry_unknown
 | _ => Except_error_inst3 LeanCageM4_Normalized_ErrorCode LeanCageM3_Result LeanCageM4_Normalized_ErrorCode_entry
 end.
Theorem imported_parse_view bytes : LeanCageM4_Normalized_parse bytes = parse_view bytes.
Proof.
 unfold LeanCageM4_Normalized_parse, parse_view.
 rewrite imported_ite_bool.
 change (OfNat_ofNat_inst1 Nat 4 (instOfNatNat 4)) with 4%Nat.
 change (OfNat_ofNat_inst1 Nat 40 (instOfNatNat 40)) with 40%Nat.
 change (OfNat_ofNat_inst1 Nat 44 (instOfNatNat 44)) with 44%Nat.
 change (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)) with 1%Nat.
 destruct (standard_bool (LeanCageM4_Normalized_headerBadBytes bytes)); [reflexivity|].
 rewrite parser_match_exact.
 destruct (LeanCageM4_Normalized_littleBytes bytes 40 4) as [|[|[|n]]]; [| | |reflexivity].
 - exact (imported_ite_le _ 2 (LeanCageM4_Normalized_littleBytes bytes 44 4)
     (Except_error_inst3 LeanCageM4_Normalized_ErrorCode LeanCageM3_Result LeanCageM4_Normalized_ErrorCode_cleanup)
     (Except_ok_inst3 LeanCageM4_Normalized_ErrorCode LeanCageM3_Result
       (LeanCageM4_Normalized_fieldsBytes bytes LeanCageM3_Entry_no))).
 - exact (imported_ite_le _ 2 (LeanCageM4_Normalized_littleBytes bytes 44 4)
     (Except_error_inst3 LeanCageM4_Normalized_ErrorCode LeanCageM3_Result LeanCageM4_Normalized_ErrorCode_cleanup)
     (Except_ok_inst3 LeanCageM4_Normalized_ErrorCode LeanCageM3_Result
       (LeanCageM4_Normalized_fieldsBytes bytes LeanCageM3_Entry_yes))).
 - exact (imported_ite_le _ 2 (LeanCageM4_Normalized_littleBytes bytes 44 4)
     (Except_error_inst3 LeanCageM4_Normalized_ErrorCode LeanCageM3_Result LeanCageM4_Normalized_ErrorCode_cleanup)
     (Except_ok_inst3 LeanCageM4_Normalized_ErrorCode LeanCageM3_Result
       (LeanCageM4_Normalized_fieldsBytes bytes LeanCageM3_Entry_unknown))).
Qed.
Definition decode_cleanup bytes entry :=
 if Nat.leb 2 (nat_of_Nat (LeanCageM4_Normalized_littleBytes bytes 44 4))
 then Except_error_inst3 LeanCageM4_Normalized_ErrorCode LeanCageM3_Result LeanCageM4_Normalized_ErrorCode_cleanup
 else LeanCageM4_Normalized_validate (LeanCageM4_Normalized_fieldsBytes bytes entry).
Definition decode_view bytes :=
 if standard_bool (LeanCageM4_Normalized_headerBadBytes bytes)
 then Except_error_inst3 LeanCageM4_Normalized_ErrorCode LeanCageM3_Result LeanCageM4_Normalized_ErrorCode_header
 else match nat_of_Nat (LeanCageM4_Normalized_littleBytes bytes 40 4) with
 | 0 => decode_cleanup bytes LeanCageM3_Entry_no
 | 1 => decode_cleanup bytes LeanCageM3_Entry_yes
 | 2 => decode_cleanup bytes LeanCageM3_Entry_unknown
 | _ => Except_error_inst3 LeanCageM4_Normalized_ErrorCode LeanCageM3_Result LeanCageM4_Normalized_ErrorCode_entry
 end.
Theorem imported_decode_view bytes : LeanCageM4_Normalized_decode bytes = decode_view bytes.
Proof.
 unfold LeanCageM4_Normalized_decode; rewrite imported_parse_view.
 unfold parse_view, decode_view.
 destruct (standard_bool (LeanCageM4_Normalized_headerBadBytes bytes)); [reflexivity|].
 destruct (nat_of_Nat (LeanCageM4_Normalized_littleBytes bytes 40 4)) as [|[|[|n]]]; [| | |reflexivity].
 all: unfold parse_cleanup, decode_cleanup.
 all: destruct (Nat.leb 2 (nat_of_Nat (LeanCageM4_Normalized_littleBytes bytes 44 4))); reflexivity.
Qed.
Theorem imported_validate_view r : LeanCageM4_Normalized_validate r =
 if standard_bool (LeanCageM3_resultValid r)
 then Except_ok_inst3 LeanCageM4_Normalized_ErrorCode LeanCageM3_Result r
 else Except_error_inst3 LeanCageM4_Normalized_ErrorCode LeanCageM3_Result LeanCageM4_Normalized_ErrorCode_validity.
Proof. unfold LeanCageM4_Normalized_validate; apply imported_ite_bool. Qed.
