(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.evidence: Universal whole-source guarantees start from independent owned inputs. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Events Globalenvs Clight.
Require Import Slice IO Machine Deterministic Library LibraryMachine LibraryPreservation LibraryControl CallProgress FreshMemory
  ResultLayout SourceGuarantees ReportingTrace DecoderValidity FrameRecord SenderSource
  SenderStorage SenderEncodingPrefix SenderEncoding SenderSelectors
  SenderReportMemory SenderReturn SenderWriteReturn SenderOutcome SenderReporting
  CopyPaths CopyTrace CopyComposition ReportPaths ReportTrace
  ReportConsequences ReportPrefixes.
Import ListNotations.
Open Scope Z_scope.
Definition sender_input cell base input ofs r digest mode mode_bytes locations :=
  frame_result_owned base input ofs r digest /\ sender_selectors cell base mode mode_bytes locations /\
  exists magic,Genv.find_symbol result_ge ___stringlit_2=Some magic /\
    readable_bytes base {|address_block:=magic;address_offset:=0|} frame_magic.
Definition sender_expected fd sequence r digest mode_bytes :=
  selected_sender_bytes fd r mode_bytes sequence (outgoing_frame sequence r digest).
Definition sender_result base expected sent value after :=
  (exists result_local bytes_local,sender_freed base result_local bytes_local after) /\
  sender_output_result expected sent value.

Definition sender_controlled_result (allow_errors : bool) base expected sent value after :=
  sender_result base expected sent value after /\ (allow_errors=true \/ value=Vint Int.zero).

Lemma sender_reporting_certificate : forall allow_errors cell base fd sequence input ofs r digest mode mode_bytes locations s,
  sender_input cell base input ofs r digest mode mode_bytes locations ->
  sender_encoding_result base fd sequence r digest Kstop s ->
  report_returns_allow allow_errors cell (sender_preserved cell base)
    (sender_controlled_result allow_errors base (sender_expected fd sequence r digest mode_bytes)) s.
Proof.
  intros allow_errors cell base fd sequence input ofs r digest mode mode_bytes locations s [OWN [SELECTORS MAGIC]]
    [result_local [bytes_local [le [after [STATE [FD [SEQ [FR [FB [NE STORAGE]]]]]]]]]];subst s.
  eapply report_returns_consequence.
  - eapply sender_reporting_source;[exact FR|exact FB|exact NE|
      eapply fresh_tls_separate;[exact (proj1 SELECTORS)|exact FR]|
      eapply fresh_tls_separate;[exact (proj1 SELECTORS)|exact FB]|exact STORAGE|exact SELECTORS|
      apply outgoing_frame_length;exact (proj1 (proj2 (proj2 (proj2 (proj2 OWN)))))|
      reflexivity|exact FD|exact SEQ].
  - intros sent value final [FREED [OUTPUT ALLOWED]];split;[split;[exists result_local,bytes_local;exact FREED|exact OUTPUT]|exact ALLOWED].
Qed.

Theorem sender_whole_source_guarantee : forall cell base fd sequence input ofs r digest mode mode_bytes locations,
  sender_input cell base input ofs r digest mode mode_bytes locations ->
  procedure_guarantee result_ge cell (sender_preserved cell base)
    (fun value after=>exists sent,sender_result base (sender_expected fd sequence r digest mode_bytes) sent value after)
    (sender_initial fd sequence input ofs Kstop base).
Proof.
  intros cell base fd sequence input ofs r digest mode mode_bytes locations INPUT.
  pose proof INPUT as [OWN [SELECTORS [magic [SYM MAGIC]]]].
  eapply copy_reaches_guarantee.
  - eapply copy_reaches_consequence;[eapply sender_encoding_connection;[exact OWN|exact SYM|exact MAGIC]|
      intros;apply old_sender_preserved;assumption|intros;exact H].
  - intros s POST;eapply procedure_guarantee_post.
    + apply report_returns_guarantee;eapply sender_reporting_certificate;[exact INPUT|exact POST].
    + intros value after [sent [RESULT ALLOWED]];exists sent;exact RESULT.
Qed.
Theorem sender_all_returns : forall cell base fd sequence input ofs r digest mode mode_bytes locations events value after,
  sender_input cell base input ofs r digest mode mode_bytes locations ->
  library_steps result_ge cell (live (sender_initial fd sequence input ofs Kstop base)) events
    (live (Returnstate value Kstop after)) ->
  sender_result base (sender_expected fd sequence r digest mode_bytes) (reporting_trace events) value after.
Proof.
  intros cell base fd sequence input ofs r digest mode mode_bytes locations events value after INPUT RUN.
  pose proof INPUT as [OWN [SELECTORS [magic [SYM MAGIC]]]].
  eapply copy_reaches_return_trace;[eapply sender_encoding_connection;[exact OWN|exact SYM|exact MAGIC]| |exact RUN].
  intros last POST;eapply report_returns_trace;eapply report_returns_consequence.
  - eapply sender_reporting_certificate;[exact INPUT|exact POST].
  - intros sent final final_mem [RESULT ALLOWED];exact RESULT.
Qed.
Theorem sender_all_prefixes : forall cell base fd sequence input ofs r digest mode mode_bytes locations events target,
  sender_input cell base input ofs r digest mode mode_bytes locations ->
  library_steps result_ge cell (live (sender_initial fd sequence input ofs Kstop base)) events target ->
  sender_preserved cell base (routine_memory target) /\
  exists rest,sender_expected fd sequence r digest mode_bytes=reporting_trace events++rest.
Proof.
  intros cell base fd sequence input ofs r digest mode mode_bytes locations events target INPUT RUN;split.
  - exact (proj1 (sender_whole_source_guarantee _ _ _ _ _ _ _ _ _ _ _ INPUT) _ _ RUN).
  - pose proof INPUT as [OWN [SELECTORS [magic [SYM MAGIC]]]].
    eapply copy_reaches_reports_prefix;[eapply sender_encoding_connection;[exact OWN|exact SYM|exact MAGIC]| |exact RUN].
    intros last POST es dest PATH.
    eapply (report_returns_prefix cell _ _ _ (sender_reporting_certificate true _ _ _ _ _ _ _ _ _ _ _ _ INPUT POST)
      (sender_expected fd sequence r digest mode_bytes) []);[|exact PATH].
    intros sent value final [[_ OUTPUT] ALLOWED];cbn;apply output_result_prefix with (value:=value);exact OUTPUT.
Qed.
Theorem sender_defined_prefix : forall cell base fd sequence input ofs r digest mode mode_bytes locations events s,
  sender_input cell base input ofs r digest mode mode_bytes locations ->
  library_steps result_ge cell (live (sender_initial fd sequence input ofs Kstop base)) events (live s) ->
  (exists value after,s=Returnstate value Kstop after /\
    exists sent,sender_result base (sender_expected fd sequence r digest mode_bytes) sent value after) \/
  (exists ev target,control_progress ev /\ library_step result_ge cell (live s) ev target).
Proof. intros;exact (proj2 (sender_whole_source_guarantee _ _ _ _ _ _ _ _ _ _ _ H) _ _ H0). Qed.
Theorem sender_returned_locals_have_no_permissions : forall cell base fd sequence input ofs r digest mode mode_bytes locations events value after,
  sender_input cell base input ofs r digest mode mode_bytes locations ->
  library_steps result_ge cell (live (sender_initial fd sequence input ofs Kstop base)) events
    (live (Returnstate value Kstop after)) ->
  exists result_local bytes_local,~Mem.valid_block base result_local /\ ~Mem.valid_block base bytes_local /\
    (forall pos kind permission,0<=pos<144 -> ~Mem.perm after result_local pos kind permission) /\
    (forall pos kind permission,0<=pos<160 -> ~Mem.perm after bytes_local pos kind permission).
Proof.
  intros. destruct (sender_all_returns _ _ _ _ _ _ _ _ _ _ _ _ _ _ H H0) as [[rl [bl FREED]] _].
  exists rl,bl;split;[exact (proj1 FREED)|]. split;[exact (proj1 (proj2 FREED))|].
  eapply sender_freed_permissions;exact FREED.
Qed.
