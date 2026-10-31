(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-m4-decoder.source: Actual typed switch selection and branch exit. *)
From Coq Require Import List.
From compcert Require Import Coqlib Values Memory Events Ctypes Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess.

Lemma certified_switch_edge : forall ge f a cases k e le m v key,
  expression_value ge e le m a v -> sem_switch_arg v (typeof a) = Some key ->
  store_edge ge (State f (Sswitch a cases) k e le m)
    (State f (seq_of_labeled_statement (select_switch key cases)) (Kswitch k) e le m).
Proof.
  intros ge f a cases k e le m v key [REAL UNIQUE] SWITCH.
  split; [exact I|]. split; [eapply step_switch; eassumption|].
  intros t other STEP; inversion STEP; subst;
    try match goal with H : _ = _ \/ _ = _ |- _ => destruct H; discriminate end.
  match goal with EV : eval_expr _ _ _ _ _ _ |- _ => pose proof (UNIQUE _ EV) as EQ; subst end.
  assert (n=key) by congruence; subst; auto.
Qed.
Lemma edge_skip_switch : forall ge f k e le m,
  edge ge (State f Sskip (Kswitch k) e le m) (State f Sskip k e le m).
Proof. intros; structural_edge. Qed.
Lemma edge_break_switch : forall ge f k e le m,
  edge ge (State f Sbreak (Kswitch k) e le m) (State f Sskip k e le m).
Proof. intros; structural_edge. Qed.
