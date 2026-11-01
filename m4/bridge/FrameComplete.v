(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-bridge.frames: Exact imported frame operations and source observations. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers.
From LeanImport Require Import Lean.
Require Import NormalizedImport BridgeBytes FrameRecord
 FrameParser FrameFields FrameDecode FrameValidity.
Local Close Scope lean_scope.
Local Open Scope Z_scope.
Definition source_frame_finish r digest entry :=
 if Nat.leb 2 (Z.to_nat (Int.unsigned (fr_clean r)))
 then Except_error_inst3 LeanCageM4_Normalized_ErrorCode LeanCageM3_Result LeanCageM4_Normalized_ErrorCode_cleanup
 else if source_frame_valid r digest entry
 then Except_ok_inst3 LeanCageM4_Normalized_ErrorCode LeanCageM3_Result (imported_frame_result r digest entry)
 else Except_error_inst3 LeanCageM4_Normalized_ErrorCode LeanCageM3_Result LeanCageM4_Normalized_ErrorCode_validity.
Definition source_complete_decode sequence r digest :=
 if negb (Nat.eqb (Z.to_nat (Int64.unsigned sequence)) 0)
 then Except_error_inst3 LeanCageM4_Normalized_ErrorCode LeanCageM3_Result LeanCageM4_Normalized_ErrorCode_header
 else match Z.to_nat (Int.unsigned (fr_entry r)) with
 | 0%nat => source_frame_finish r digest LeanCageM3_Entry_no
 | 1%nat => source_frame_finish r digest LeanCageM3_Entry_yes
 | 2%nat => source_frame_finish r digest LeanCageM3_Entry_unknown
 | _ => Except_error_inst3 LeanCageM4_Normalized_ErrorCode LeanCageM3_Result LeanCageM4_Normalized_ErrorCode_entry
 end.
Lemma source_frame_finish_exact r digest entry : source_frame_cleanup r digest entry = source_frame_finish r digest entry.
Proof.
 unfold source_frame_cleanup,source_frame_finish.
 rewrite imported_validate_view, imported_frame_validity; reflexivity.
Qed.
Theorem source_complete_decode_exact sequence r digest : source_frame_decode sequence r digest = source_complete_decode sequence r digest.
Proof.
 unfold source_frame_decode,source_complete_decode.
 destruct (negb (Nat.eqb (Z.to_nat (Int64.unsigned sequence)) 0)); [reflexivity|].
 destruct (Z.to_nat (Int.unsigned (fr_entry r))) as [|[|[|n]]]; try reflexivity; apply source_frame_finish_exact.
Qed.
Theorem imported_complete_frame sequence r digest : length digest=32%nat ->
 LeanCageM4_Normalized_decode (imported_bytes (outgoing_frame sequence r digest)) = source_complete_decode sequence r digest.
Proof. intro LEN; rewrite imported_frame_decode by exact LEN; apply source_complete_decode_exact. Qed.
