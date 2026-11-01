(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-bridge.frames: Exact imported frame operations and source observations. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Integers.
From LeanImport Require Import Lean.
Require Import NormalizedImport BridgeNat BridgeBytes
 FrameRecord WireFields FrameLists FrameNumbers
 FrameFields FrameHeader FrameParser.
Local Close Scope lean_scope.
Local Open Scope Z_scope.

Lemma standard_bool_not b : standard_bool (Bool_not b) = negb (standard_bool b).
Proof. destruct b; reflexivity. Qed.
Definition source_frame_cleanup r digest entry :=
 if Nat.leb 2 (Z.to_nat (Int.unsigned (fr_clean r)))
 then Except_error_inst3 LeanCageM4_Normalized_ErrorCode LeanCageM3_Result LeanCageM4_Normalized_ErrorCode_cleanup
 else LeanCageM4_Normalized_validate (imported_frame_result r digest entry).
Definition source_frame_decode sequence r digest :=
 if negb (Nat.eqb (Z.to_nat (Int64.unsigned sequence)) 0)
 then Except_error_inst3 LeanCageM4_Normalized_ErrorCode LeanCageM3_Result LeanCageM4_Normalized_ErrorCode_header
 else match Z.to_nat (Int.unsigned (fr_entry r)) with
 | 0%nat => source_frame_cleanup r digest LeanCageM3_Entry_no
 | 1%nat => source_frame_cleanup r digest LeanCageM3_Entry_yes
 | 2%nat => source_frame_cleanup r digest LeanCageM3_Entry_unknown
 | _ => Except_error_inst3 LeanCageM4_Normalized_ErrorCode LeanCageM3_Result LeanCageM4_Normalized_ErrorCode_entry
 end.
Theorem imported_frame_decode sequence r digest : length digest = 32%nat ->
 LeanCageM4_Normalized_decode (imported_bytes (outgoing_frame sequence r digest)) =
 source_frame_decode sequence r digest.
Proof.
 intro LEN; rewrite imported_decode_view.
 unfold decode_view, source_frame_decode.
 rewrite imported_frame_header by exact LEN.
 rewrite standard_bool_not, imported_beq_exact.
 unfold imported_int64; rewrite nat2Natid.
 change (40)%Nat with (Nat_of_nat 40); change (4)%Nat with (Nat_of_nat 4).
 rewrite imported_little32_value, wire_entry.
 unfold imported_int32; rewrite nat2Natid.
 cbn [nat_of_Nat].
 destruct (negb (Nat.eqb (Z.to_nat (Int64.unsigned sequence)) 0)); [reflexivity|].
 destruct (Z.to_nat (Int.unsigned (fr_entry r))) as [|[|[|n]]]; [| | |reflexivity].
 all: unfold decode_cleanup, source_frame_cleanup.
 all: rewrite imported_frame_fields by exact LEN.
 all: change (44)%Nat with (Nat_of_nat 44); change (4)%Nat with (Nat_of_nat 4).
 all: rewrite imported_little32_value, wire_clean.
 all: unfold imported_int32; rewrite nat2Natid; reflexivity.
Qed.
