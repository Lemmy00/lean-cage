(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-wire.private: Source returns for actual sender frames, including late rejection mutation. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers Values Memory Clight.
Require Import Machine Deterministic LibraryMachine ResultLayout FreshMemory FrameRecord DecoderLayout
  DecoderSource DecoderInput DecoderValidity DecoderProgram
  WireFields WireLayout WireValidity WireDecoded.
Import ListNotations.
Open Scope Z_scope.
Theorem wire_frame_length_shape : forall sequence r digest,
  length(outgoing_frame sequence r digest)=(128+length digest)%nat.
Proof.
  intros;unfold outgoing_frame;rewrite !app_length,!frame_word32_length,!frame_word64_length,!repeat_length.
  cbn [frame_magic length];lia.
Qed.
Lemma wire_int64_eq : forall x y,Int64.eq x y=true <-> x=y.
Proof. intros;split;[apply Int64.same_if_eq|intros;subst;apply Int64.eq_true]. Qed.
Theorem wire_header_fields : forall sequence r digest run expected_sequence,
  length digest=32%nat ->
  (header_valid(outgoing_frame sequence r digest)run expected_sequence=true <->
    fr_run r=run /\ sequence=expected_sequence).
Proof. intros;rewrite wire_header_exact by assumption;rewrite andb_true_iff,!wire_int64_eq;reflexivity. Qed.
Definition wire_decode_result base output ofs sequence r digest run uid preflight expected_sequence value after :=
  value=Vint(if wire_accepts sequence r digest run uid preflight expected_sequence then Int.zero else Int.mone) /\
  (fr_run r=run /\ sequence=expected_sequence ->
    frame_result_contents after output ofs(wire_decoded_record r)(repeat Byte.zero 32)) /\
  (fr_run r<>run \/ sequence<>expected_sequence -> old_memory base after) /\
  exists local before,~Mem.valid_block base local /\ Mem.free before local 0 144=Some after.
Theorem wire_decoder_source_return : forall cell base p output ofs sequence r digest run uid preflight expected_sequence events value after,
  decoder_input base p(outgoing_frame sequence r digest)output ofs run uid preflight ->
  library_steps result_ge cell(live(decoder_initial p expected_sequence output ofs Kstop base))events
    (live(Returnstate value Kstop after)) ->
  wire_decode_result base output ofs sequence r digest run uid preflight expected_sequence value after.
Proof.
  intros cell base p output ofs sequence r digest run uid preflight expected_sequence events value after INPUT RUN.
  assert(LEN : length digest=32%nat).
  { pose proof(proj1 INPUT)as LENGTH;rewrite wire_frame_length_shape in LENGTH;lia. }
  destruct(decoder_all_returns cell base p _ output ofs run uid preflight expected_sequence events value after INPUT RUN)
    as[VALUE[CONTENT[OLD FREE]]].
  split.
  - rewrite <-wire_decoder_acceptance by exact LEN;exact VALUE.
  - split.
    + intros MATCH. apply(proj1(wire_decoded_contents after output ofs sequence r digest)).
      apply CONTENT;apply(proj2(wire_header_fields _ _ _ _ _ LEN));exact MATCH.
    + split;[|exact FREE]. intros DIFFERENT;apply OLD.
      destruct(header_valid(outgoing_frame sequence r digest)run expected_sequence)eqn:HEADER;[|reflexivity].
      apply(proj1(wire_header_fields _ _ _ _ _ LEN))in HEADER;tauto.
Qed.
