(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-decoder.source: Compose the whole decoder after its actual comparison return. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Slice Machine ClightSteps WriteAll StoreSteps CallPaths Library ResultLayout ResultSource ResultSafety
  FreshMemory FrameBytes DecoderLayout DecoderSource DecoderMemory DecoderCompare
  DecoderHeader DecoderZeros DecoderCommon DecoderTags DecoderValidity DecoderInput
  DecoderPayload SourcePaths SourceReach SourceConsequences.
Import ListNotations.
Open Scope Z_scope.
Definition decoder_return_result bytes run uid preflight sequence (early late : mem) value after :=
  value = Vint (if decoder_accepts bytes run uid preflight sequence then Int.zero else Int.mone) /\
  after = if header_valid bytes run sequence then late else early.

Theorem decoder_after_comparison_source : forall (cell : tls) base p bytes output ofs run uid preflight sequence
    (memories : decoder_memories base output ofs bytes) comparison,
  decoder_input base p bytes output ofs run uid preflight ->
  Int.eq comparison Int.zero = magic_matches bytes ->
  source_returns result_ge (result_preserved base output ofs)
    (decoder_return_result bytes run uid preflight sequence
      (decoder_early _ _ _ _ memories) (decoder_late _ _ _ _ memories))
    (Returnstate (Vint comparison)
      (decoder_compare_cont (decoder_local _ _ _ _ memories) (decoder_temps p sequence output ofs))
      (decoder_allocated _ _ _ _ memories)).
Proof.
  intros cell base p bytes output ofs run uid preflight sequence memories comparison INPUT CMP.
  destruct memories as [allocated local built copied early late ALLOC STORAGE EARLY LATE OLD EARLYOLD LATEP LATECONT].
  cbn. destruct INPUT as [LEN [READ [DEST [SEP [magic [rb [ub [pb [GLOBALS [USEP PSEP]]]]]]]]]].
  destruct GLOBALS as [MS [RS [US [PS [MAGIC [RUN [UID PRE]]]]]]].
  destruct STORAGE as [FRESH [LOCAL [STORES [COPY [CONTENTS [RANGE [PA PC]]]]]]].
  assert (PE : result_preserved base output ofs early) by (apply old_decoder_preserved;exact EARLYOLD).
  assert (RA : readable_bytes allocated p bytes) by (eapply old_memory_readable; eassumption).
  assert (RC : readable_bytes copied p bytes) by (exact (frame_preserved_readable base copied p bytes output ofs READ SEP PC)).
  assert (RUN' : Mem.load Mint64 allocated rb 0=Some (Vlong run)) by (eapply old_memory_load; eassumption).
  assert (UID' : Mem.load Mint32 copied ub 0=Some (Vint uid)) by (eapply decoder_outside_load; [exact PC|eassumption|eassumption]).
  assert (PRE' : Mem.load Mint32 copied pb 0=Some (Vint preflight)) by (eapply decoder_outside_load; [exact PC|eassumption|eassumption]).
  assert (HEADER : header_matches comparison bytes run sequence = header_prefix bytes run sequence).
  { unfold header_matches,header_prefix. rewrite CMP; reflexivity. }
  eapply source_reaches_returns.
  - eapply source_reaches_consequence.
    + apply (decoder_header_source_path cell allocated early local p bytes run rb sequence output ofs
        (decoder_temps p sequence output ofs) comparison RA LEN RS RUN');
        [unfold decoder_temps;WriteAll.lookup|unfold decoder_temps;WriteAll.lookup|
         unfold decoder_temps;WriteAll.lookup|exact EARLY].
    + intros m [SAME|SAME]; subst m; assumption.
    + intros last POST;exact POST.
  - intros target [[SAME BAD]|[le [SAME [PTR [SEQ [OUT GOOD]]]]]]; subst target.
    + apply source_returns_done; [exact PE|].
      unfold decoder_return_result,decoder_accepts,header_valid; rewrite <-HEADER,BAD;split;reflexivity.
    + eapply source_returns_prepend; [exact PA|apply unchanged_store_edge;WriteAll.structural|].
      change decoder_tail with (Ssequence decoder_tail_reserved decoder_payload).
      eapply source_returns_prepend; [exact PA|apply unchanged_store_edge;WriteAll.structural|].
      rewrite decoder_header_reserved_source.
      eapply source_reaches_returns.
      * eapply source_reaches_consequence.
        -- exact (zero_scan_source_reaches allocated early local p bytes output ofs
            (Kseq decoder_payload Kstop) _i _t'95 156 160 le RA LEN ltac:(lia)
            ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
            ltac:(discriminate) ltac:(discriminate) EARLY PTR OUT).
        -- intros m [SAME|SAME];subst m;assumption.
        -- intros last POST;exact POST.
      * intros target [[i [BOUND [NE [PREFIX SAME]]]]|[nextle [SAME [PTR' [OUT' ZERO]]]]]; subst target.
        -- apply source_returns_done; [exact PE|].
           unfold decoder_return_result,decoder_accepts,header_valid;
             rewrite <-HEADER,GOOD,(zero_test_rejects bytes 156 160 i BOUND NE);split;reflexivity.
        -- assert (HEAD : header_valid bytes run sequence=true).
           { unfold header_valid;rewrite <-HEADER,GOOD,(proj2 (zero_test_true bytes 156 160 ltac:(lia)) ZERO);reflexivity. }
           eapply source_returns_prepend; [exact PA|apply unchanged_store_edge;WriteAll.structural|].
           change decoder_payload with (Ssequence decoder_construction decoder_postchecks).
           eapply source_returns_prepend; [exact PA|apply unchanged_store_edge;WriteAll.structural|].
           destruct (decoder_construction_source_path cell (result_preserved base output ofs)
             allocated local built copied output ofs p bytes (Kseq decoder_postchecks Kstop) nextle
             PTR' OUT' LEN STORES COPY PA PC) as [count [finalle [PATH [PTR'' OUT'']]]].
           { intros m PRES;exact (frame_preserved_readable base m p bytes output ofs READ SEP PRES). }
           { intros; eapply result_local_store_preserves;eassumption. }
           eapply source_returns_path; [exact PATH|].
           eapply source_returns_prepend; [exact PC|apply unchanged_store_edge;WriteAll.structural|].
           destruct DEST as [LOW [HIGH [ALIGN WRITE]]].
           eapply source_returns_consequence.
           ++ exact (decoder_payload_source copied late local p bytes uid ub preflight pb output ofs finalle
               LOW HIGH CONTENTS RC LEN US UID' PS PRE' PTR'' OUT'' LATE).
           ++ intros m [SAME|SAME];subst m;assumption.
           ++ intros value after [VALUE MEM]. unfold decoder_return_result,decoder_accepts.
              rewrite HEAD;cbn. unfold decoder_payload_accepts in VALUE. auto.
Qed.
