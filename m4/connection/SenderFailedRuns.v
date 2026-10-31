(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.evidence: A nonempty expected report can fail without emitting any byte. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers Values Memory Clight.
Require Import Machine Fault LibraryMachine ResultLayout ReportingTrace FrameRecord SenderSource
  SenderEncoding SenderProgram CopyPaths CopyTrace ReportFailedRuns.
Import ListNotations.
Open Scope Z_scope.
Theorem sender_failed_report_exists : forall cell base fd sequence input ofs r digest mode mode_bytes locations error,
  sender_input cell base input ofs r digest mode mode_bytes locations ->
  sender_expected fd sequence r digest mode_bytes<>[] -> error<>Int.repr 4 ->
  exists events after,
    library_steps result_ge cell (live (sender_initial fd sequence input ofs Kstop base)) events
      (live (Returnstate (Vint Int.mone) Kstop after)) /\
    reporting_trace events=[] /\ sender_result base (sender_expected fd sequence r digest mode_bytes) [] (Vint Int.mone) after.
Proof.
  intros cell base fd sequence input ofs r digest mode mode_bytes locations error INPUT NONEMPTY ERROR.
  pose proof INPUT as [OWN [SELECTORS [magic [SYM MAGIC]]]].
  destruct (copy_reaches_quiet_run result_ge cell _ _ _
    (sender_encoding_connection base fd sequence input ofs r digest Kstop magic OWN SYM MAGIC))
    as [before [last [PREFIX [PROGRESS [EMPTY POST]]]]].
  destruct (report_empty_finite_return cell _ _ _ error
    (sender_reporting_certificate true cell base fd sequence input ofs r digest mode mode_bytes locations last INPUT POST) ERROR)
    as [rest [value [after [TAIL [EMPTYTAIL [RESULT ALLOWED]]]]]].
  assert (VALUE : value=Vint Int.mone).
  { destruct RESULT as [_ [[VALUE BYTES]|[VALUE FAILED]]];[congruence|exact VALUE]. }
  subst value;exists (before++rest),after;split;[eapply library_steps_trans;eassumption|].
  rewrite reporting_trace_app,EMPTY,EMPTYTAIL;auto.
Qed.
