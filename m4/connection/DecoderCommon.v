(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-decoder.source: Actual common payload checks after output construction. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Slice Machine ClightSteps WriteAll StoreSteps LocalAccess CallAccess Library
  ResultLayout ResultSource FrameBytes DecoderLayout DecoderSource DecoderFields
  DecoderControl SourceReach.
Import ListNotations.
Open Scope Z_scope.

Definition common_valid bytes uid :=
  negb (Int.ltu (Int.repr 7) (byte_word_at bytes 6)) &&
  negb (Int.ltu (Int.repr 2) (word32_at bytes 40)) &&
  negb (Int.ltu (Int.repr 1) (word32_at bytes 44)) &&
  Int.eq (word32_at bytes 52) uid && Int.eq (word32_at bytes 48) (Int.repr 0) &&
  Int64.eq (word64_at bytes 56) (Int64.repr 0) &&
  Int64.eq (word64_at bytes 64) (Int64.repr 0) &&
  Int64.eq (word64_at bytes 72) (Int64.repr 0) &&
  Int64.eq (word64_at bytes 80) (Int64.repr 0).
Definition decoder_common := match decoder_postchecks with Ssequence s _ => s | _ => Sskip end.
Definition decoder_after_common := match decoder_postchecks with Ssequence _ s => s | _ => Sskip end.
Theorem decoder_common_parts : decoder_postchecks = Ssequence decoder_common decoder_after_common.
Proof. reflexivity. Qed.
Definition common_boundary local p output ofs m freed bytes uid s :=
  (s = Returnstate (Vint Int.mone) Kstop freed /\ common_valid bytes uid = false) \/
  (exists le, s = State f_decode_frame Sskip (Kseq decoder_after_common Kstop) (decoder_env local) le m /\
    le ! _p = Some (address_value p) /\ le ! _r = Some (Vptr output (Ptrofs.repr ofs)) /\
    common_valid bytes uid = true).

Lemma decoder_common_source_path : forall m freed local p bytes uid ub output ofs le,
  0 <= ofs -> ofs+144 <= Ptrofs.modulus -> decoded_contents m output ofs bytes ->
  Genv.find_symbol result_ge _run_uid = Some ub -> Mem.load Mint32 m ub 0 = Some (Vint uid) ->
  le ! _p = Some (address_value p) -> le ! _r = Some (Vptr output (Ptrofs.repr ofs)) ->
  Mem.free m local 0 144 = Some freed ->
  source_reaches result_ge (fun after => after=m \/ after=freed)
    (common_boundary local p output ofs m freed bytes uid)
    (State f_decode_frame decoder_common (Kseq decoder_after_common Kstop) (decoder_env local) le m).
Proof.
  intros m freed local p bytes uid ub output ofs le LOW HIGH CONTENT US UID PTR OUT FREE.
  unfold decoder_common, decoder_postchecks, decoder_payload, decoder_tail; cbn [fn_body].
  Ltac common_truth :=
    unfold common_valid; unfold Int.one, Int.zero, Int64.zero in *;
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
  Ltac common_done := lazymatch goal with
    | |- source_reaches _ _ _ (Returnstate _ Kstop _) =>
      apply source_reaches_done; [right;reflexivity|];
      unfold common_boundary; left; split; [reflexivity|common_truth]
    | |- source_reaches _ _ _ (State _ Sskip (Kseq decoder_after_common Kstop) _ _ _) =>
      apply source_reaches_done; [left;reflexivity|];
      unfold common_boundary; right; eexists; split; [reflexivity|];
      split; [WriteAll.lookup|]; split; [WriteAll.lookup|common_truth]
    end.
  Ltac common_return FREE := eapply source_reaches_prepend; [left;reflexivity| |];
    [eapply decoder_local_return;
      [apply old_expression_value; decoder_control_expression|reflexivity|exact FREE]|].
  Ltac common_field bytes LOW HIGH CONTENT := lazymatch goal with
    | |- source_reaches _ _ _ (State _ (Sset _ (Efield _ ?field _)) _ _ _ _) =>
      let chosen := decoder_field_cell bytes field in
      eapply source_reaches_prepend; [left;reflexivity| |];
      [eapply certified_set_edge; eapply (decoder_field_value _ _ _ _ _ bytes _ _ chosen);
        [WriteAll.lookup|exact LOW|exact HIGH|exact CONTENT|
         unfold decoded_cells; cbn [In app]; tauto|reflexivity|reflexivity]|]
    end.
  Ltac common_global US UID := eapply source_reaches_prepend; [left;reflexivity| |];
    [eapply certified_set_edge; eapply location_read_value;
      [eapply global_location_value; [unfold decoder_env, result_env; cbn;reflexivity|exact US]|
       eapply deref_loc_value; [reflexivity|cbn;exact UID]]|].
  Ltac common_run bytes LOW HIGH CONTENT US UID FREE :=
    try match goal with H : _ = true |- _ => discriminate H
      | H : _ = false |- _ => discriminate H end; cbn [call_cont];
    lazymatch goal with
    | |- source_reaches _ _ _ (Returnstate _ Kstop _) => common_done
    | |- source_reaches _ _ _ (State _ Sskip (Kseq decoder_after_common Kstop) _ _ _) => common_done
    | _ => first
      [common_return FREE|common_field bytes LOW HIGH CONTENT|common_global US UID|
       decoder_reach_route|decoder_reach_set|
       decoder_reach_if;
         try lazymatch goal with |- source_reaches _ _ _ (State _ (if ?b then _ else _) _ _ _ _) =>
           let CHOICE := fresh "CHOICE" in destruct b eqn:CHOICE end|
         fail 100 "No common payload step"];
      common_run bytes LOW HIGH CONTENT US UID FREE
    end.
  common_run bytes LOW HIGH CONTENT US UID FREE.
Qed.
