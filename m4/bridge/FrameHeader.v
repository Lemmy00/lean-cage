(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-bridge.frames: Exact imported frame operations and source observations. *)
From Stdlib Require Import ZArith List Lia Bool.
From compcert Require Import Integers.
From LeanImport Require Import Lean.
Require Import NormalizedImport BridgeNat BridgeBytes BridgeWords
 DecoderValidity FrameRecord WireFields WireLayout FrameSlices FrameNumbers.
Local Close Scope lean_scope.
Local Open Scope Z_scope.
Import ListNotations.

Lemma imported_size_value bs : ByteArray_size (imported_bytes bs) = Nat_of_nat (length bs).
Proof. apply imported_nat_injective; rewrite imported_size_exact, nat2Natid; reflexivity. Qed.
Theorem imported_frame_magic sequence r digest :
 ByteArray_extract (imported_bytes (outgoing_frame sequence r digest)) 0 4 = imported_bytes frame_magic.
Proof.
 change (ByteArray_extract (imported_bytes (outgoing_frame sequence r digest)) (Nat_of_nat 0) (Nat_of_nat 4) = imported_bytes frame_magic).
 rewrite imported_extract_exact; cbn [Nat.sub skipn]; now rewrite wire_first_four.
Qed.
Theorem imported_frame_header sequence r digest : length digest = 32%nat ->
 LeanCageM4_Normalized_headerBadBytes (imported_bytes (outgoing_frame sequence r digest)) =
 Bool_not (Nat_beq (imported_int64 sequence) Nat_zero).
Proof.
 intro LEN; unfold LeanCageM4_Normalized_headerBadBytes.
 rewrite imported_size_value, outgoing_frame_length by exact LEN.
 rewrite imported_frame_magic, imported_frame_version, imported_frame_terminal by exact LEN.
 change (OfNat_ofNat_inst1 Nat 4 (instOfNatNat 4)) with (Nat_of_nat 4).
 change (OfNat_ofNat_inst1 Nat 8 (instOfNatNat 8)) with (Nat_of_nat 8).
 change (OfNat_ofNat_inst1 Nat 16 (instOfNatNat 16)) with (Nat_of_nat 16).
 change (OfNat_ofNat_inst1 Nat 24 (instOfNatNat 24)) with (Nat_of_nat 24).
 change (OfNat_ofNat_inst1 Nat 28 (instOfNatNat 28)) with (Nat_of_nat 28).
 rewrite (imported_little64_value (outgoing_frame sequence r digest) 16), wire_sequence.
 rewrite (imported_little32_value (outgoing_frame sequence r digest) 24), wire_payload.
 rewrite (imported_little32_value (outgoing_frame sequence r digest) 28), wire_reserved.
 change (Bool_or (Bool_or (Bool_or (Bool_or (Bool_or (Bool_or Bool_false Bool_false) Bool_false)
   (Bool_not (Nat_beq (imported_int64 sequence) Nat_zero))) Bool_false) Bool_false) Bool_false =
   Bool_not (Nat_beq (imported_int64 sequence) Nat_zero)).
 destruct (Nat_beq (imported_int64 sequence) Nat_zero); reflexivity.
Qed.
