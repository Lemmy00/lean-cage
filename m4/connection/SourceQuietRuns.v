(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-sender.evidence: Source-only suffixes have concrete executions without publication bytes. *)
From Coq Require Import List.
From compcert Require Import Values Memory Events Clight.
Require Import Machine StoreSteps LibraryMachine LibraryPreservation SourcePaths ReportingTrace.
Import ListNotations.
Lemma source_steps_report_nothing : forall n,
  reporting_trace (map original_event (repeat (source_step E0) n))=[].
Proof. induction n;cbn;auto. Qed.
Theorem source_returns_quiet_run : forall ge cell P R start,
  source_returns ge P R start -> exists events value after,
    library_steps ge cell (live start) events (live (Returnstate value Kstop after)) /\
    reporting_trace events=[] /\ R value after.
Proof.
  intros ge cell P R start [n [value [after [PATH POST]]]].
  exists (map original_event (repeat (source_step E0) n)),value,after;split.
  - apply original_runs_preserved;eapply store_path_actual;exact PATH.
  - split;[apply source_steps_report_nothing|exact POST].
Qed.
