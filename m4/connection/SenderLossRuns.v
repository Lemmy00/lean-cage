(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.evidence: Actual partial transfer followed by loss after arbitrary waits. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers Values Memory Clight.
Require Import IO Machine Fault Library LibraryMachine WriteMemory WriteAll WriteCallers ResultLayout ReportingTrace
  FrameRecord SenderSource SenderEncoding SenderProgram SenderReportMemory
  CopyPaths CopyTrace ReportFirstWrite.
Import ListNotations.
Open Scope Z_scope.
Theorem sender_one_byte_loss_exists : forall waits cell base fd sequence input ofs r digest mode mode_bytes locations,
  sender_input cell base input ofs r digest mode mode_bytes locations ->
  sender_expected fd sequence r digest mode_bytes<>[] ->
  exists events final byte rest,
    library_steps result_ge cell (live (sender_initial fd sequence input ofs Kstop base)) events (dead final) /\
    reporting_trace events=[byte] /\ sender_expected fd sequence r digest mode_bytes=byte::rest /\
    sender_preserved cell base final /\
    exists before request,events=before++map original_event (repeat wait_step waits++[partial_loss request [byte] None]).
Proof.
  intros waits cell base fd sequence input ofs r digest mode mode_bytes locations INPUT NONEMPTY.
  pose proof INPUT as [OWN [SELECTORS [magic [SYM MAGIC]]]].
  destruct (copy_reaches_quiet_run result_ge cell _ _ _
    (sender_encoding_connection base fd sequence input ofs r digest Kstop magic OWN SYM MAGIC))
    as [before [last [PREFIX [PROGRESS [EMPTY POST]]]]].
  destruct (report_first_write_or_return false cell _ _ _
    (sender_reporting_certificate false cell base fd sequence input ofs r digest mode mode_bytes locations last INPUT POST))
    as [[events [value [after [RUN [NOTHING [[FREED OUTPUT] ALLOWED]]]]]]|
      [leading [q [bytes [m [suffix [WRITE [QUIET [CELL [WOWN [BYTES CALL]]]]]]]]]]].
  - destruct ALLOWED as [IMPOSSIBLE|VALUE];[discriminate|subst value].
    destruct OUTPUT as [[VALUE EQ]|[VALUE FAILED]];[congruence|discriminate].
  - destruct bytes as [|byte restbytes];[contradiction|].
    destruct (write_caller_partial_loss waits q [byte] restbytes m suffix WOWN ltac:(discriminate) CALL)
      as [loss [LOSS [SENT [REPLIES [n EVENTS]]]]].
    rewrite CELL in LOSS.
    assert (RUN : library_steps result_ge cell (live (sender_initial fd sequence input ofs Kstop base))
      (before++leading++map original_event loss) (dead m)).
    { eapply library_steps_trans;[exact PREFIX|]. eapply library_steps_trans;[exact WRITE|exact LOSS]. }
    assert (TRACE : reporting_trace (before++leading++map original_event loss)=[byte]).
    { rewrite !reporting_trace_app,EMPTY,QUIET,reporting_trace_original;exact SENT. }
    destruct (sender_all_prefixes _ _ _ _ _ _ _ _ _ _ _ _ _ INPUT RUN) as [PRESERVED [rest BOUND]].
    rewrite TRACE in BOUND.
    exists (before++leading++map original_event loss),m,byte,rest.
    split;[exact RUN|]. split;[exact TRACE|]. split;[exact BOUND|]. split;[exact PRESERVED|].
    exists (before++leading++map original_event (repeat (Machine.source_step Events.E0) n)),(WriteAll.suffix q 0).
    rewrite EVENTS,map_app,!app_assoc;reflexivity.
Qed.
