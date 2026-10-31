(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.evidence: Construct a complete finite run from every independently owned input. *)
From Coq Require Import List.
From compcert Require Import Integers Values Memory Clight.
Require Import Machine Fault LibraryMachine LibraryControl ResultLayout ReportingTrace FrameRecord SenderSource
  SenderEncoding SenderProgram CopyPaths CopyTrace ReportRuns.
Import ListNotations.
Theorem sender_finite_return_exists : forall cell base fd sequence input ofs r digest mode mode_bytes locations,
  sender_input cell base input ofs r digest mode mode_bytes locations ->
  exists events value after,
    library_steps result_ge cell (live (sender_initial fd sequence input ofs Kstop base)) events
      (live (Returnstate value Kstop after)) /\
    sender_result base (sender_expected fd sequence r digest mode_bytes) (reporting_trace events) value after.
Proof.
  intros cell base fd sequence input ofs r digest mode mode_bytes locations INPUT.
  pose proof INPUT as [OWN [SELECTORS [magic [SYM MAGIC]]]].
  destruct (copy_reaches_quiet_run result_ge cell _ _ _
    (sender_encoding_connection base fd sequence input ofs r digest Kstop magic OWN SYM MAGIC))
    as [before [last [PREFIX [PROGRESS [EMPTY POST]]]]].
  destruct (report_returns_run _ _ _ _ (sender_reporting_certificate true _ _ _ _ _ _ _ _ _ _ _ _ INPUT POST))
    as [rest [value [after [TAIL [RESULT ALLOWED]]]]].
  exists (before++rest),value,after;split;[eapply library_steps_trans;eassumption|].
  rewrite reporting_trace_app,EMPTY;exact RESULT.
Qed.
