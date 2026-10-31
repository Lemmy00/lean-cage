(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.evidence: Complete publication witnesses use actual source and actual successful writes. *)
From Coq Require Import List.
From compcert Require Import Integers Values Memory Clight.
Require Import Machine Fault LibraryMachine ResultLayout ReportingTrace FrameRecord SenderSource
  SenderEncoding SenderProgram CopyPaths CopyTrace ReportSuccessfulRuns.
Import ListNotations.
Theorem sender_complete_report_exists : forall cell base fd sequence input ofs r digest mode mode_bytes locations,
  sender_input cell base input ofs r digest mode mode_bytes locations ->
  exists events after,
    library_steps result_ge cell (live (sender_initial fd sequence input ofs Kstop base)) events
      (live (Returnstate (Vint Int.zero) Kstop after)) /\
    reporting_trace events=sender_expected fd sequence r digest mode_bytes /\
    sender_result base (sender_expected fd sequence r digest mode_bytes) (reporting_trace events) (Vint Int.zero) after.
Proof.
  intros cell base fd sequence input ofs r digest mode mode_bytes locations INPUT.
  pose proof INPUT as [OWN [SELECTORS [magic [SYM MAGIC]]]].
  destruct (copy_reaches_quiet_run result_ge cell _ _ _
    (sender_encoding_connection base fd sequence input ofs r digest Kstop magic OWN SYM MAGIC))
    as [before [last [PREFIX [PROGRESS [EMPTY POST]]]]].
  destruct (report_allowed_finite_return false cell _ _ _
    (sender_reporting_certificate false cell base fd sequence input ofs r digest mode mode_bytes locations last INPUT POST))
    as [rest [value [after [TAIL [RESULT ALLOWED]]]]].
  destruct ALLOWED as [IMPOSSIBLE|VALUE];[discriminate|subst value].
  assert (BYTES : reporting_trace rest=sender_expected fd sequence r digest mode_bytes).
  { destruct RESULT as [_ [[VALUE BYTES]|[VALUE FAILED]]];[exact BYTES|discriminate]. }
  exists (before++rest),after;split;[eapply library_steps_trans;eassumption|].
  rewrite reporting_trace_app,EMPTY;split;assumption.
Qed.
