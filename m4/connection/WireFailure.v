(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-wire.failure: Complete eight-byte reports retain their actual source words. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import FrameBytes FrameRecord FailureMemoryDraft FailureBranchesDraft FailureContractDraft FailureTrace
  WireWords.
Import ListNotations.
Open Scope Z_scope.
Theorem wire_failure_packet : forall stage error,
  failure_packet stage error=frame_word32 stage++frame_word32 error.
Proof. intros;unfold failure_packet,frame_word32;rewrite map_app;reflexivity. Qed.
Theorem wire_failure_fields : forall stage error,
  word32_at(failure_packet stage error)0=stage /\ word32_at(failure_packet stage error)4=error.
Proof.
  intros;rewrite wire_failure_packet;split;[apply wire_word32_head|].
  rewrite wire_word32_skip,wire_skip_past by(rewrite frame_word32_length;lia).
  change(word32_at(frame_word32 error++[])0=error);apply wire_word32_head.
Qed.
Theorem wire_selected_report_bound : forall mode_bytes stage error,
  (length(selected_report mode_bytes stage error)<=8)%nat.
Proof.
  intros;unfold selected_report;destruct(matches_mode mode_bytes error_drop_bytes);[cbn;lia|].
  rewrite firstn_length,failure_packet_length;apply Nat.le_min_r.
Qed.
Theorem wire_selected_eight : forall mode_bytes stage error,
  length(selected_report mode_bytes stage error)=8%nat ->
  selected_report mode_bytes stage error=failure_packet stage error.
Proof.
  intros mode_bytes stage error LEN;unfold selected_report in *.
  destruct(matches_mode mode_bytes error_drop_bytes);[discriminate LEN|].
  destruct(matches_mode mode_bytes error_short_bytes);cbn [failure_count]in *.
  - rewrite firstn_length,failure_packet_length in LEN;discriminate LEN.
  - change(firstn 8(failure_packet stage error)=failure_packet stage error).
    rewrite <-(failure_packet_length stage error);apply firstn_all.
Qed.
Theorem wire_eight_byte_prefix_exact : forall mode_bytes stage error bytes rest,
  selected_report mode_bytes stage error=bytes++rest -> length bytes=8%nat ->
  bytes=failure_packet stage error /\ rest=[].
Proof.
  intros mode_bytes stage error bytes rest PREFIX LEN.
  pose proof(wire_selected_report_bound mode_bytes stage error)as BOUND.
  rewrite PREFIX,app_length,LEN in BOUND.
  assert(REST : rest=[]). { destruct rest;[reflexivity|cbn in BOUND;lia]. }
  subst rest;rewrite app_nil_r in PREFIX.
  split;[|reflexivity]. rewrite <-PREFIX;apply wire_selected_eight;rewrite PREFIX;exact LEN.
Qed.
