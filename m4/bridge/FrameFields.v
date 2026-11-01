(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-bridge.frames: Exact imported frame operations and source observations. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers.
From LeanImport Require Import Lean.
Require Import NormalizedImport BridgeNat BridgeBytes BridgeWords
 FrameRecord WireFields WireLayout FrameSlices FrameNumbers.
Local Close Scope lean_scope.
Local Open Scope Z_scope.
Import ListNotations.

Definition imported_frame_result r digest entry :=
 LeanCageM3_Result_mk (imported_int32 (Int.zero_ext 8 (fr_kind r)))
   (imported_int32 (fr_stage r)) (imported_int32 (fr_detail r)) entry
   (Nat_beq (imported_int32 (fr_clean r)) 1)
   (imported_int32 (fr_triggers r)) (imported_int32 (fr_uid r))
   (imported_int64 (fr_run r)) (imported_int64 (fr_cpu r)) (imported_int64 (fr_peak r))
   (imported_int64 (fr_out r)) (imported_int64 (fr_err r)) (imported_int64 (fr_elapsed r))
   (imported_int32 (fr_export_state r)) (imported_int32 (fr_omitted r))
   (imported_bytes digest) (imported_int64 (fr_oom r)) (imported_int64 (fr_pids r))
   (imported_int32 (fr_export_error r)).
Theorem imported_frame_fields sequence r digest entry : length digest = 32%nat ->
 LeanCageM4_Normalized_fieldsBytes (imported_bytes (outgoing_frame sequence r digest)) entry =
 imported_frame_result r digest entry.
Proof.
 intro LEN; unfold LeanCageM4_Normalized_fieldsBytes, imported_frame_result.
 rewrite imported_frame_kind.
 change (OfNat_ofNat_inst1 Nat 4 (instOfNatNat 4)) with (Nat_of_nat 4).
 change (OfNat_ofNat_inst1 Nat 8 (instOfNatNat 8)) with (Nat_of_nat 8).
 change (OfNat_ofNat_inst1 Nat 32 (instOfNatNat 32)) with (Nat_of_nat 32).
 change (OfNat_ofNat_inst1 Nat 36 (instOfNatNat 36)) with (Nat_of_nat 36).
 change (OfNat_ofNat_inst1 Nat 44 (instOfNatNat 44)) with (Nat_of_nat 44).
 change (OfNat_ofNat_inst1 Nat 48 (instOfNatNat 48)) with (Nat_of_nat 48).
 change (OfNat_ofNat_inst1 Nat 52 (instOfNatNat 52)) with (Nat_of_nat 52).
 change (OfNat_ofNat_inst1 Nat 56 (instOfNatNat 56)) with (Nat_of_nat 56).
 change (OfNat_ofNat_inst1 Nat 64 (instOfNatNat 64)) with (Nat_of_nat 64).
 change (OfNat_ofNat_inst1 Nat 72 (instOfNatNat 72)) with (Nat_of_nat 72).
 change (OfNat_ofNat_inst1 Nat 80 (instOfNatNat 80)) with (Nat_of_nat 80).
 change (OfNat_ofNat_inst1 Nat 88 (instOfNatNat 88)) with (Nat_of_nat 88).
 change (OfNat_ofNat_inst1 Nat 96 (instOfNatNat 96)) with (Nat_of_nat 96).
 change (OfNat_ofNat_inst1 Nat 100 (instOfNatNat 100)) with (Nat_of_nat 100).
 change (OfNat_ofNat_inst1 Nat 104 (instOfNatNat 104)) with (Nat_of_nat 104).
 change (OfNat_ofNat_inst1 Nat 136 (instOfNatNat 136)) with (Nat_of_nat 136).
 change (OfNat_ofNat_inst1 Nat 144 (instOfNatNat 144)) with (Nat_of_nat 144).
 change (OfNat_ofNat_inst1 Nat 152 (instOfNatNat 152)) with (Nat_of_nat 152).
 rewrite (imported_little32_value (outgoing_frame sequence r digest) 32).
 rewrite (imported_little32_value (outgoing_frame sequence r digest) 36).
 rewrite (imported_little32_value (outgoing_frame sequence r digest) 44).
 rewrite (imported_little32_value (outgoing_frame sequence r digest) 48).
 rewrite (imported_little32_value (outgoing_frame sequence r digest) 52).
 rewrite (imported_little32_value (outgoing_frame sequence r digest) 96).
 rewrite (imported_little32_value (outgoing_frame sequence r digest) 100).
 rewrite (imported_little32_value (outgoing_frame sequence r digest) 152).
 rewrite (imported_little64_value (outgoing_frame sequence r digest) 8).
 rewrite (imported_little64_value (outgoing_frame sequence r digest) 56).
 rewrite (imported_little64_value (outgoing_frame sequence r digest) 64).
 rewrite (imported_little64_value (outgoing_frame sequence r digest) 72).
 rewrite (imported_little64_value (outgoing_frame sequence r digest) 80).
 rewrite (imported_little64_value (outgoing_frame sequence r digest) 88).
 rewrite (imported_little64_value (outgoing_frame sequence r digest) 136).
 rewrite (imported_little64_value (outgoing_frame sequence r digest) 144).
 rewrite wire_stage, wire_detail, wire_clean, wire_triggers, wire_uid,
   wire_export_state, wire_omitted, wire_run, wire_cpu, wire_peak, wire_out, wire_err, wire_elapsed.
 destruct (wire_late_fields sequence r digest LEN) as [OOM [PIDS ERROR]].
 rewrite OOM, PIDS, ERROR.
 rewrite (imported_extract_exact (outgoing_frame sequence r digest) 104 136).
 change (136-104)%nat with 32%nat; rewrite wire_digest_exact by exact LEN.
 reflexivity.
Qed.
