(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-decoder.source: The actual short-circuit header checks, including early local free. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Slice Machine ClightSteps WriteAll StoreSteps LocalAccess CallAccess CallPaths Library Readers
  ResultLayout ResultSource FrameBytes DecoderSource DecoderCompare DecoderControl
  SourceReach SequencePaths.
Import ListNotations.
Open Scope Z_scope.

Definition header_matches comparison bytes run sequence :=
  Int.eq comparison Int.zero && Int.eq (byte_word_at bytes 4) Int.one &&
  Int.eq (byte_word_at bytes 5) Int.zero && Int.eq (byte_word_at bytes 7) Int.zero &&
  Int64.eq (word64_at bytes 8) run && Int64.eq (word64_at bytes 16) sequence &&
  Int.eq (word32_at bytes 24) (Int.repr 128) && Int.eq (word32_at bytes 28) Int.zero.
Definition header_boundary local p sequence output ofs m freed comparison bytes run s :=
  (s = Returnstate (Vint Int.mone) Kstop freed /\ header_matches comparison bytes run sequence = false) \/
  (exists le, s = State f_decode_frame Sskip (Kseq decoder_tail Kstop) (decoder_env local) le m /\
    le ! _p = Some (address_value p) /\ le ! _sequence = Some (Vlong sequence) /\
    le ! _r = Some (Vptr output (Ptrofs.repr ofs)) /\ header_matches comparison bytes run sequence = true).

Lemma decoder_header_source_path : forall (cell : tls) m freed local p bytes run rb sequence output ofs le comparison,
  readable_bytes m p bytes -> length bytes = 160%nat ->
  Genv.find_symbol result_ge _run_id = Some rb -> Mem.load Mint64 m rb 0 = Some (Vlong run) ->
  le ! _p = Some (address_value p) -> le ! _sequence = Some (Vlong sequence) ->
  le ! _r = Some (Vptr output (Ptrofs.repr ofs)) ->
  Mem.free m local 0 144 = Some freed ->
  source_reaches result_ge (fun after => after = m \/ after = freed)
    (header_boundary local p sequence output ofs m freed comparison bytes run)
    (Returnstate (Vint comparison) (decoder_compare_cont local le) m).
Proof.
  intros cell m freed local p bytes run rb sequence output ofs le comparison
    READ LEN RS RUN PTR SEQ OUT FREE.
  destruct decoder_reader_symbols as [b32 [b64 [S32 [F32 [S64 F64]]]]].
  unfold decoder_compare_cont, decoder_header; cbn [fn_body sequence_continuation].
  Ltac header_truth :=
    unfold header_matches; unfold Int.one, Int.zero, Int64.zero in *;
    cbn [cast_int_int Int.cmp Int.cmpu Int64.cmp Int64.cmpu] in *;
    change (Int.sub (Int.repr 160) (Int.repr 32)) with (Int.repr 128) in *;
    repeat rewrite cast_bool_zero_test in *;
    repeat rewrite bool_value_zero_test in *;
    repeat match goal with
      | H : negb _ = true |- _ => apply Bool.negb_true_iff in H
      | H : negb _ = false |- _ => apply Bool.negb_false_iff in H
    end;
    repeat match goal with
      | H : ?b = true |- _ => progress rewrite H
      | H : ?b = false |- _ => progress rewrite H
    end; reflexivity.
  Ltac header_done := lazymatch goal with
    | |- source_reaches _ _ _ (Returnstate _ Kstop _) =>
      apply source_reaches_done; [right;reflexivity|];
      unfold header_boundary; left; split; [reflexivity|header_truth]
    | |- source_reaches _ _ _ (State _ Sskip (Kseq decoder_tail Kstop) _ _ _) =>
      apply source_reaches_done; [left;reflexivity|];
      unfold header_boundary; right; eexists; split; [reflexivity|];
      split; [WriteAll.lookup|]; split; [WriteAll.lookup|]; split; [WriteAll.lookup|];
      header_truth
    end.
  Ltac header_return FREE := eapply source_reaches_prepend; [left;reflexivity| |];
    [eapply decoder_local_return;
      [apply old_expression_value; decoder_control_expression|reflexivity|exact FREE]|].
  Ltac header_byte m p bytes READ LEN := lazymatch goal with
    | |- source_reaches _ _ _ (State _ (Sset _ (Ederef
        (Ebinop Oadd _ (Econst_int ?offset _) _) _)) _ _ _ _) =>
      let n := eval vm_compute in (Z.to_nat (Int.signed offset)) in
      eapply source_reaches_prepend; [left;reflexivity|apply unchanged_store_edge|];
      [eapply edge_set with (v := Vint (byte_word_at bytes n));
        eapply value_load; [decoder_control_expression|reflexivity|];
        change (Mem.loadv Mint8unsigned m (Vptr (address_block p)
          (Ptrofs.add (Ptrofs.repr (address_offset p)) (Ptrofs.repr (Z.of_nat n)))) =
          Some (Vint (byte_word_at bytes n)));
        rewrite pointer_add_representations;
        exact (readable_byte_load m p bytes n READ ltac:(rewrite LEN; lia))|]
    end.
  Ltac header_global RS RUN := eapply source_reaches_prepend; [left;reflexivity| |];
    [eapply certified_set_edge; eapply location_read_value;
      [eapply global_location_value; [unfold decoder_env, result_env; cbn;reflexivity|exact RS]|
       eapply deref_loc_value; [reflexivity|cbn;exact RUN]]|].
  Ltac header_call symbol function := eapply source_reaches_prepend; [left;reflexivity| |];
    [eapply certified_call_edge; [reflexivity|
      apply old_expression_value; eapply value_function;
        [unfold decoder_env, result_env; cbn;reflexivity|exact symbol|reflexivity]|
      decoder_arguments|exact function|reflexivity]|].
  Ltac header_reader cell m p bytes READ LEN symbol function n count INPUT :=
    header_call symbol function;
    match goal with |- context [Ptrofs.mul ?a ?b] =>
      change (Ptrofs.mul a b) with (Ptrofs.repr (Z.of_nat n)) end;
    rewrite pointer_add_representations;
    eapply source_reaches_path;
    [eapply (reader_caller_path result_ge cell);
      [exact (INPUT m p bytes n READ ltac:(rewrite LEN;lia))|left;reflexivity]|].
  Ltac header_word cell m p bytes READ LEN S32 F32 S64 F64 := lazymatch goal with
    | |- source_reaches _ _ _ (State _ (Scall _ (Evar _get32 _)
        [Ebinop Oadd _ (Econst_int ?offset _) _]) _ _ _ _) =>
      let n := eval vm_compute in (Z.to_nat (Int.signed offset)) in
      header_reader cell m p bytes READ LEN S32 F32 n 59%nat frame_reader32_input
    | |- source_reaches _ _ _ (State _ (Scall _ (Evar _get64 _)
        [Ebinop Oadd _ (Econst_int ?offset _) _]) _ _ _ _) =>
      let n := eval vm_compute in (Z.to_nat (Int.signed offset)) in
      header_reader cell m p bytes READ LEN S64 F64 n 103%nat frame_reader64_input
    end.
  Ltac header_run cell m p bytes READ LEN RS RUN S32 F32 S64 F64 FREE :=
    try match goal with H : _ = true |- _ => discriminate H
      | H : _ = false |- _ => discriminate H end; cbn [call_cont];
    lazymatch goal with
    | |- source_reaches _ _ _ (Returnstate _ Kstop _) => header_done
    | |- source_reaches _ _ _ (State _ Sskip (Kseq decoder_tail Kstop) _ _ _) => header_done
    | _ => first
      [header_return FREE
      |header_byte m p bytes READ LEN
      |header_word cell m p bytes READ LEN S32 F32 S64 F64
      |header_global RS RUN
      |decoder_reach_route
      |decoder_reach_set
      |decoder_reach_if;
        try lazymatch goal with |- source_reaches _ _ _ (State _ (if ?b then _ else _) _ _ _ _) =>
          let CHOICE := fresh "CHOICE" in destruct b eqn:CHOICE end
      |fail 100 "No decoder control step"];
      header_run cell m p bytes READ LEN RS RUN S32 F32 S64 F64 FREE
    end.
  header_run cell m p bytes READ LEN RS RUN S32 F32 S64 F64 FREE.
Qed.
