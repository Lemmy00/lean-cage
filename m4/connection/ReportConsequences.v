(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.reporting: Preserve checked source certificates when specializing byte results. *)
From Coq Require Import List.
From compcert Require Import Integers Values Memory Clight.
Require Import ReportPaths SourceReach StoreSteps.
Theorem report_returns_consequence : forall allow_errors cell P R S s,
  report_returns_allow allow_errors cell P R s ->
  (forall bytes value after,R bytes value after -> S bytes value after) -> report_returns_allow allow_errors cell P S s.
Proof.
  intros allow_errors cell P R S s SCRIPT;revert S;induction SCRIPT;intros S POST.
  - apply report_returns_done;[exact H|apply POST;exact H0].
  - eapply report_returns_source;[exact H|exact H0|apply (IHSCRIPT S);exact POST].
  - eapply report_returns_selector;[exact H|exact H0|exact H1|exact H2|apply (IHSCRIPT S);exact POST].
  - eapply report_returns_write;[exact H|exact H0|exact H1|exact H2|exact H3|exact H4|].
    intros events value after HISTORY WRITE ALLOWED;apply (H6 events value after HISTORY WRITE ALLOWED
      (fun more final last=>S (WriteAll.emitted_trace events++more) final last)).
    intros more final last RESULT;apply POST;exact RESULT.
Qed.
Theorem source_reaches_report : forall allow_errors cell P Q R s,
  source_reaches report_ge P Q s -> (forall last,Q last -> report_returns_allow allow_errors cell P R last) ->
  report_returns_allow allow_errors cell P R s.
Proof.
  intros allow_errors cell P Q R s [count [last [PATH POST]]] NEXT.
  eapply report_returns_path;[exact PATH|apply NEXT;exact POST].
Qed.
