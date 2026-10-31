(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-decoder.source: Composition of all checks after the output assignment. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Slice Machine ClightSteps WriteAll StoreSteps Library ResultLayout
  FrameBytes DecoderLayout DecoderSource DecoderControl DecoderCommon
  DecoderZeros DecoderTags DecoderValidity SourcePaths SourceReach.
Import ListNotations.
Open Scope Z_scope.
Definition decoder_payload_accepts bytes uid preflight :=
  common_valid bytes uid && zero_test bytes 96 156 && tag_valid bytes preflight.
Definition payload_result bytes uid preflight (freed : mem) value after :=
  value=Vint (if decoder_payload_accepts bytes uid preflight then Int.zero else Int.mone) /\ after=freed.
Ltac decoder_return_route := eapply source_returns_prepend;
  [first [assumption|left;reflexivity]|apply unchanged_store_edge;WriteAll.structural|].

Theorem decoder_after_common_source : forall m freed local p bytes uid preflight pb output ofs le,
  0 <= ofs -> ofs+144 <= Ptrofs.modulus -> decoded_contents m output ofs bytes ->
  readable_bytes m p bytes -> length bytes=160%nat -> common_valid bytes uid=true ->
  Genv.find_symbol result_ge _preflight=Some pb -> Mem.load Mint32 m pb 0=Some (Vint preflight) ->
  le ! _p=Some (address_value p) -> le ! _r=Some (Vptr output (Ptrofs.repr ofs)) ->
  Mem.free m local 0 144=Some freed ->
  source_returns result_ge (fun after => after=m \/ after=freed)
    (payload_result bytes uid preflight freed)
    (State f_decode_frame decoder_after_common Kstop (decoder_env local) le m).
Proof.
  intros m freed local p bytes uid preflight pb output ofs le LOW HIGH CONTENT READ LEN COMMON PS PRE PTR OUT FREE.
  rewrite decoder_tag_parts. decoder_return_route.
  rewrite decoder_payload_reserved_source.
  eapply source_reaches_returns.
  - apply (zero_scan_source_reaches m freed local p bytes output ofs
      (Kseq (Ssequence decoder_tag_section decoder_zero_return) Kstop) _i__1 _t'83 96 156 le
      READ LEN ltac:(lia) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
      ltac:(discriminate) ltac:(discriminate) FREE PTR OUT).
  - intros target [[i [RANGE [NE [PREFIX SAME]]]]|[nextle [SAME [PTR' [OUT' ZERO]]]]]; subst target.
    + apply source_returns_done; [right;reflexivity|]. unfold payload_result,decoder_payload_accepts.
      rewrite COMMON,(zero_test_rejects bytes 96 156 i RANGE NE); split;reflexivity.
    + pose proof (proj2 (zero_test_true bytes 96 156 ltac:(lia)) ZERO) as TEST.
      decoder_return_route. decoder_return_route.
      eapply source_reaches_returns.
      * exact (decoder_tags_source_path m freed local bytes uid preflight pb output ofs nextle
          LOW HIGH CONTENT COMMON PS PRE OUT' FREE).
      * intros final [[SAME TAG]|[SAME TAG]]; subst final;
          apply source_returns_done; [right;reflexivity| |right;reflexivity|];
          unfold payload_result,decoder_payload_accepts; rewrite COMMON,TEST,TAG; split;reflexivity.
Qed.

Theorem decoder_payload_source : forall m freed local p bytes uid ub preflight pb output ofs le,
  0 <= ofs -> ofs+144 <= Ptrofs.modulus -> decoded_contents m output ofs bytes ->
  readable_bytes m p bytes -> length bytes=160%nat ->
  Genv.find_symbol result_ge _run_uid=Some ub -> Mem.load Mint32 m ub 0=Some (Vint uid) ->
  Genv.find_symbol result_ge _preflight=Some pb -> Mem.load Mint32 m pb 0=Some (Vint preflight) ->
  le ! _p=Some (address_value p) -> le ! _r=Some (Vptr output (Ptrofs.repr ofs)) ->
  Mem.free m local 0 144=Some freed ->
  source_returns result_ge (fun after => after=m \/ after=freed)
    (payload_result bytes uid preflight freed)
    (State f_decode_frame decoder_postchecks Kstop (decoder_env local) le m).
Proof.
  intros m freed local p bytes uid ub preflight pb output ofs le LOW HIGH CONTENT READ LEN US UID PS PRE PTR OUT FREE.
  rewrite decoder_common_parts. decoder_return_route.
  eapply source_reaches_returns.
  - exact (decoder_common_source_path m freed local p bytes uid ub output ofs le
      LOW HIGH CONTENT US UID PTR OUT FREE).
  - intros target [[SAME BAD]|[nextle [SAME [PTR' [OUT' GOOD]]]]]; subst target.
    + apply source_returns_done; [right;reflexivity|]. unfold payload_result,decoder_payload_accepts.
      rewrite BAD;split;reflexivity.
    + decoder_return_route.
      exact (decoder_after_common_source m freed local p bytes uid preflight pb output ofs nextle
        LOW HIGH CONTENT READ LEN GOOD PS PRE PTR' OUT' FREE).
Qed.
