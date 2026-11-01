(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-bridge.frames: Exact imported frame operations and source observations. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Integers.
From LeanImport Require Import Lean.
Require Import NormalizedImport BridgeNat BridgeBytes
 FrameRecord FrameLists FrameEquality FrameSlices
 FrameHeader FrameFields FrameNumbers FrameParser FrameDecode FrameLogic.
Local Close Scope lean_scope.
Local Open Scope Z_scope.
Import ListNotations.

Definition source_kind_valid kind stage detail entry clean triggers run uid :=
 match Z.to_nat kind with
 | 0%nat => Z.eqb stage 0 && Z.leb detail 255 && entry_equal entry LeanCageM3_Entry_yes
 | 1%nat => Z.leb 1 stage && Z.leb stage 8 && Z.ltb 0 detail && Z.leb detail 4095 && entry_equal entry LeanCageM3_Entry_no
 | 2%nat => Z.eqb stage 0 && Z.ltb 0 detail && Z.leb detail 64 && entry_equal entry LeanCageM3_Entry_yes
 | 3%nat => Z.eqb stage 0 && Z.eqb detail 0 && Z.ltb 0 triggers
 | 4%nat => Z.eqb stage 9 && Z.ltb 0 detail && Z.leb detail 4095
 | 7%nat => Z.eqb stage 0 && Z.eqb detail 0 && entry_equal entry LeanCageM3_Entry_no &&
   Z.eqb run 0 && Z.eqb uid 0 && clean && Z.eqb triggers 0
 | _ => false end.
Definition source_frame_valid r digest entry :=
 let kind := Int.unsigned (Int.zero_ext 8 (fr_kind r)) in
 let triggers := Int.unsigned (fr_triggers r) in
 let exportState := Int.unsigned (fr_export_state r) in
 let exportError := Int.unsigned (fr_export_error r) in
 let run := Int64.unsigned (fr_run r) in
 let uid := Int.unsigned (fr_uid r) in
 (Z.leb kind 4 || Z.eqb kind 7) && Z.leb triggers 63 && Z.leb exportState 3 &&
 Z.leb exportError 4095 && (if Z.ltb exportState 2 then Z.eqb exportError 0 else Z.ltb 0 exportError) &&
 ((negb (Z.eqb kind 0) && negb (Z.eqb kind 2) && negb (Z.eqb kind 3)) || Z.ltb 0 run) &&
 Nat.eqb (length digest) 32 && (Z.eqb exportState 1 || source_bytes_equal digest (repeat Byte.zero 32)) &&
 ((Z.eqb run 0 && Z.eqb uid 0) || (Z.ltb 0 run && Z.leb 100000 uid && Z.leb uid 100999)) &&
 source_kind_valid kind (Int.unsigned (fr_stage r)) (Int.unsigned (fr_detail r)) entry
   (Z.eqb (Int.unsigned (fr_clean r)) 1) triggers run uid.
Theorem imported_frame_validity r digest entry :
 standard_bool (LeanCageM3_resultValid (imported_frame_result r digest entry)) = source_frame_valid r digest entry.
Proof.
 unfold LeanCageM3_resultValid, imported_frame_result.
 cbv beta iota zeta delta [LeanCageM3_Result_kind LeanCageM3_Result_stage LeanCageM3_Result_detail
 LeanCageM3_Result_entry LeanCageM3_Result_clean LeanCageM3_Result_triggers LeanCageM3_Result_uid
 LeanCageM3_Result_run LeanCageM3_Result_exportState LeanCageM3_Result_exportError LeanCageM3_Result_exportDigest
 NormalizedImport.kind NormalizedImport.stage NormalizedImport.detail NormalizedImport.entry NormalizedImport.clean
 NormalizedImport.triggers NormalizedImport.uid NormalizedImport.run NormalizedImport.exportState
 NormalizedImport.exportError NormalizedImport.exportDigest].
 change (LE_le_inst1 Nat instLENat) with Nat_le.
 change (LT_lt_inst1 Nat instLTNat) with (fun a b => Nat_le (Nat_succ a) b).
 change (GT_gt_inst1 Nat instLTNat) with (fun a b => Nat_le (Nat_succ b) a).
 cbv beta.
 rewrite validity_match_exact.
 repeat rewrite standard_bool_and.
 repeat rewrite standard_bool_or.
 rewrite standard_bool_kind_match.
 change (BEq_beq_inst1 Nat (instBEqOfDecidableEq_inst1 Nat instDecidableEqNat)) with Nat_beq.
 change (BEq_beq_inst1 ByteArray ByteArray_instBEq) with ByteArray_beq.
 unfold bne_inst1.
 change (BEq_beq_inst1 Nat (instBEqOfDecidableEq_inst1 Nat instDecidableEqNat)) with Nat_beq.
 repeat rewrite standard_bool_and.
 repeat rewrite standard_bool_or.
 repeat rewrite standard_bool_not.
 rewrite imported_ite_lt_number, standard_bool_if.
 repeat rewrite imported_decLt_number.
 repeat rewrite imported_decLe_number.
 repeat rewrite imported_beq_number.
 repeat rewrite imported_entry_equal.
 change (OfNat_ofNat_inst1 Nat 32 (instOfNatNat 32)) with 32%Nat.
 rewrite imported_zero_digest, imported_byte_equality_bool.
 repeat rewrite imported_int32_number.
 repeat rewrite imported_int64_number.
 rewrite imported_size_value, imported_nat_number.
 unfold imported_int32; rewrite nat2Natid.
 change (natural_value (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))) with 0.
 change (natural_value (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))) with 1.
 change (natural_value (OfNat_ofNat_inst1 Nat 2 (instOfNatNat 2))) with 2.
 change (natural_value (OfNat_ofNat_inst1 Nat 3 (instOfNatNat 3))) with 3.
 change (natural_value (OfNat_ofNat_inst1 Nat 4 (instOfNatNat 4))) with 4.
 change (natural_value (OfNat_ofNat_inst1 Nat 7 (instOfNatNat 7))) with 7.
 change (natural_value (OfNat_ofNat_inst1 Nat 8 (instOfNatNat 8))) with 8.
 change (natural_value (OfNat_ofNat_inst1 Nat 9 (instOfNatNat 9))) with 9.
 change (natural_value (OfNat_ofNat_inst1 Nat 32 (instOfNatNat 32))) with 32.
 change (natural_value (OfNat_ofNat_inst1 Nat 63 (instOfNatNat 63))) with 63.
 change (natural_value (OfNat_ofNat_inst1 Nat 64 (instOfNatNat 64))) with 64.
 change (natural_value (OfNat_ofNat_inst1 Nat 255 (instOfNatNat 255))) with 255.
 change (natural_value (OfNat_ofNat_inst1 Nat 4095 (instOfNatNat 4095))) with 4095.
 change (natural_value (OfNat_ofNat_inst1 Nat 100000 (instOfNatNat 100000))) with 100000.
 change (natural_value (OfNat_ofNat_inst1 Nat 100999 (instOfNatNat 100999))) with 100999.
 change (natural_value 1) with 1; change (natural_value 32) with 32.
 unfold source_frame_valid, source_kind_valid.
 rewrite ZifyBool.Z_of_nat_eqb_iff.
 reflexivity.
Qed.
