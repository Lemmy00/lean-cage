(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-bridge.frames: Exact imported frame operations and source observations. *)
From Stdlib Require Import Arith List Lia Bool.
From LeanImport Require Import Lean.
Require Import NormalizedImport BridgeNat BridgeBytes
 FrameLists FrameHeader FrameParser FrameDecode.
Local Close Scope lean_scope.
Local Open Scope nat_scope.
Lemma standard_bool_injective a b : standard_bool a = standard_bool b -> a = b.
Proof. destruct a,b; simpl; congruence. Qed.
Theorem imported_bad_length_header bs : length bs <> 160 ->
 LeanCageM4_Normalized_headerBadBytes (imported_bytes bs) = Bool_true.
Proof.
 intro LEN; unfold LeanCageM4_Normalized_headerBadBytes; rewrite imported_size_value.
 assert (BAD : bne_inst1 Nat (instBEqOfDecidableEq_inst1 Nat instDecidableEqNat)
   (Nat_of_nat (length bs)) (OfNat_ofNat_inst1 Nat 160 (instOfNatNat 160)) = Bool_true).
 { apply standard_bool_injective.
   change (standard_bool (Bool_not (Nat_beq (Nat_of_nat (length bs)) 160)) = true).
   rewrite standard_bool_not, imported_beq_exact, nat2Natid.
   change (negb (Nat.eqb (length bs) 160) = true).
   apply negb_true_iff; apply Nat.eqb_neq; exact LEN. }
 rewrite BAD; reflexivity.
Qed.
Theorem imported_bad_length_rejected bs : length bs <> 160 ->
 LeanCageM4_Normalized_decode (imported_bytes bs) =
 Except_error_inst3 LeanCageM4_Normalized_ErrorCode LeanCageM3_Result LeanCageM4_Normalized_ErrorCode_header.
Proof. intro LEN; rewrite imported_decode_view; unfold decode_view; rewrite imported_bad_length_header by exact LEN; reflexivity. Qed.
