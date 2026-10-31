(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-decoder.source: Exact sequence continuations and local returns for decoder control. *)
From Coq Require Import List.
From compcert Require Import Values Memory Events Clight.
Require Import Machine ClightSteps StoreSteps CallPaths SourcePaths.

Fixpoint sequence_statement s := match s with
  Ssequence first rest => sequence_statement first | _ => s end.
Fixpoint sequence_continuation s k := match s with
  Ssequence first rest => sequence_continuation first (Kseq rest k) | _ => k end.
Fixpoint sequence_depth s := match s with
  Ssequence first rest => S (sequence_depth first) | _ => O end.
Theorem source_sequence_path : forall ge P f s k e le m,
  P m -> store_path ge P (State f s k e le m) (sequence_depth s)
    (State f (sequence_statement s) (sequence_continuation s k) e le m).
Proof.
  intros ge P f s; induction s; intros k env0 regs mem0 GOOD; cbn;
    try (constructor; exact GOOD).
  eapply store_next; [exact GOOD|apply unchanged_store_edge; apply edge_seq|apply IHs1; exact GOOD].
Qed.
Theorem source_sequence_returns : forall ge P R f s k e le m,
  P m -> source_returns ge P R
    (State f (sequence_statement s) (sequence_continuation s k) e le m) ->
  source_returns ge P R (State f s k e le m).
Proof. intros; eapply source_returns_path; [apply source_sequence_path; eassumption|eassumption]. Qed.
