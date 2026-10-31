(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-decoder.source: Private tag acceptance follows the actual switch and its break/return paths. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Slice Machine ClightSteps WriteAll StoreSteps LocalAccess CallAccess Library
  ResultLayout ResultSource FrameBytes DecoderLayout DecoderSource DecoderFields
  DecoderControl DecoderCommon DecoderZeros SourceReach SwitchControl.
Import ListNotations.
Open Scope Z_scope.

Definition tag_valid bytes preflight :=
  let stage := word32_at bytes 32 in let detail := word32_at bytes 36 in
  let entry := word32_at bytes 40 in let clean := word32_at bytes 44 in
  match Int.unsigned (byte_word_at bytes 6) with
  | 0 => Int.eq stage (Int.repr 0) && negb (Int.ltu (Int.repr 255) detail) && Int.eq entry (Int.repr 1)
  | 1 => negb (Int.ltu stage (Int.repr 1)) && negb (Int.ltu (Int.repr 8) stage) &&
      negb (Int.eq detail (Int.repr 0)) && negb (Int.ltu (Int.repr 4095) detail) && Int.eq entry (Int.repr 0)
  | 2 => Int.eq stage (Int.repr 0) && negb (Int.eq detail (Int.repr 0)) &&
      negb (Int.ltu (Int.repr 64) detail) && Int.eq entry (Int.repr 1)
  | 4 => Int.eq stage (Int.repr 9) && negb (Int.eq detail (Int.repr 0)) &&
      negb (Int.ltu (Int.repr 4095) detail)
  | 5 => Int.eq stage (Int.repr 0) && Int.eq detail (Int.repr 0) && Int.eq entry (Int.repr 0) &&
      Int.eq clean (Int.repr 0) && negb (Int64.eq (word64_at bytes 88) (Int64.repr 0))
  | 6 => Int.eq stage (Int.repr 8) && Int.eq detail (Int.repr 0) && Int.eq entry (Int.repr 1) &&
      Int.eq clean (Int.repr 0)
  | 7 => negb (Int.eq preflight (Int.repr 0)) && Int.eq stage (Int.repr 0) &&
      Int.eq detail (Int.repr 0) && Int.eq entry (Int.repr 0)
  | _ => false
  end.
Definition decoder_tag_section := match decoder_after_common with
  Ssequence _ (Ssequence tag _) => tag | _ => Sskip end.
Definition decoder_zero_return := match decoder_after_common with
  Ssequence _ (Ssequence _ ret) => ret | _ => Sskip end.
Definition decoder_cases := match decoder_tag_section with
  Ssequence _ (Sswitch _ cases) => cases | _ => LSnil end.
Theorem decoder_tag_parts : decoder_after_common =
  Ssequence DecoderZeros.decoder_payload_reserved
    (Ssequence decoder_tag_section decoder_zero_return).
Proof. reflexivity. Qed.

Lemma common_kind_bound : forall bytes uid,
  common_valid bytes uid = true -> 0 <= Int.unsigned (byte_word_at bytes 6) <= 7.
Proof.
  intros bytes uid VALID. unfold common_valid in VALID.
  repeat rewrite andb_true_iff in VALID.
  assert (KIND : negb (Int.ltu (Int.repr 7) (byte_word_at bytes 6)) = true) by tauto.
  apply negb_true_iff in KIND. unfold Int.ltu in KIND.
  change ((if zlt 7 (Int.unsigned (byte_word_at bytes 6)) then true else false) = false) in KIND.
  destruct (zlt 7 (Int.unsigned (byte_word_at bytes 6))); [discriminate|].
  pose proof (Int.unsigned_range (byte_word_at bytes 6)); lia.
Qed.
Lemma small_tag_cases : forall tag, 0 <= tag <= 7 ->
  tag=0 \/ tag=1 \/ tag=2 \/ tag=3 \/ tag=4 \/ tag=5 \/ tag=6 \/ tag=7.
Proof. intros; lia. Qed.

Definition tag_boundary freed bytes preflight s :=
  (s = Returnstate (Vint Int.zero) Kstop freed /\ tag_valid bytes preflight = true) \/
  (s = Returnstate (Vint Int.mone) Kstop freed /\ tag_valid bytes preflight = false).

Theorem decoder_tags_source_path : forall m freed local bytes uid preflight pb output ofs le,
  0 <= ofs -> ofs+144 <= Ptrofs.modulus -> decoded_contents m output ofs bytes ->
  common_valid bytes uid = true ->
  Genv.find_symbol result_ge _preflight = Some pb -> Mem.load Mint32 m pb 0 = Some (Vint preflight) ->
  le ! _r = Some (Vptr output (Ptrofs.repr ofs)) -> Mem.free m local 0 144 = Some freed ->
  source_reaches result_ge (fun after => after=m \/ after=freed)
    (tag_boundary freed bytes preflight)
    (State f_decode_frame decoder_tag_section (Kseq decoder_zero_return Kstop) (decoder_env local) le m).
Proof.
  intros m freed local bytes uid preflight pb output ofs le LOW HIGH CONTENT VALID PS PRE OUT FREE.
  unfold decoder_tag_section, decoder_after_common, decoder_postchecks, decoder_payload, decoder_tail;
    cbn [fn_body].
  decoder_reach_route. common_field bytes LOW HIGH CONTENT. decoder_reach_route.
  eapply source_reaches_prepend; [left;reflexivity| |].
  - eapply certified_switch_edge; [apply old_expression_value; decoder_control_expression|reflexivity].
  - destruct (small_tag_cases _ (common_kind_bound bytes uid VALID))
      as [KEY|[KEY|[KEY|[KEY|[KEY|[KEY|[KEY|KEY]]]]]]]; rewrite KEY;
      cbn [select_switch select_switch_case select_switch_default seq_of_labeled_statement].

    Ltac tag_truth KEY :=
      unfold tag_valid; rewrite KEY; cbv beta iota zeta;
      unfold Int.one, Int.zero, Int64.zero in *;
      cbn [cast_int_int Int.cmp Int.cmpu Int64.cmp Int64.cmpu] in *;
      repeat rewrite cast_bool_zero_test in *; repeat rewrite bool_value_zero_test in *;
      repeat match goal with
        | H : negb _ = true |- _ => apply Bool.negb_true_iff in H
        | H : negb _ = false |- _ => apply Bool.negb_false_iff in H
      end;
      repeat match goal with
        | H : ?b = true |- _ => progress rewrite H
        | H : ?b = false |- _ => progress rewrite H
      end; reflexivity.
    Ltac tag_done KEY := apply source_reaches_done; [right;reflexivity|];
      unfold tag_boundary; first
      [left;split;[reflexivity|tag_truth KEY]
      |right;split;[reflexivity|tag_truth KEY]].
    Ltac tag_route := eapply source_reaches_prepend; [left;reflexivity|apply unchanged_store_edge|];
      [first [WriteAll.structural|apply edge_skip_switch|apply edge_break_switch]|].
    Ltac tag_run bytes LOW HIGH CONTENT PS PRE FREE KEY :=
      try match goal with H : _ = true |- _ => discriminate H
        | H : _ = false |- _ => discriminate H end; cbn [call_cont];
      lazymatch goal with
      | |- source_reaches _ _ _ (Returnstate _ Kstop _) => tag_done KEY
      | _ => first
        [common_return FREE|common_field bytes LOW HIGH CONTENT|common_global PS PRE|
         tag_route|decoder_reach_set|
         decoder_reach_if;
           try lazymatch goal with |- source_reaches _ _ _ (State _ (if ?b then _ else _) _ _ _ _) =>
             let CHOICE := fresh "CHOICE" in destruct b eqn:CHOICE end|
           fail 100 "No private tag step"];
        tag_run bytes LOW HIGH CONTENT PS PRE FREE KEY
      end.
    all: tag_run bytes LOW HIGH CONTENT PS PRE FREE KEY.
Qed.
