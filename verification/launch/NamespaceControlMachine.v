(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Actual namespace primitive transitions retain checked source control. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From EntryProcess Require Import ProcessControl ProcessControlMachine.
From EntryNamespace Require Import NamespaceMachine.

Section SOURCE_CALLER.
Variable permitted : expr -> list expr -> bool.

Theorem checked_namespace_step (ge : genv) cell :
  (forall address fn, Genv.find_funct ge address = Some (Internal fn) ->
    checked_statement permitted (fn_body fn) = true) ->
  forall before event after,
    checked_machine permitted before -> namespace_step ge cell before event after ->
    checked_machine permitted after.
Proof.
  intros FUNCTIONS before event after GOOD STEP; inversion STEP; subst; cbn in *; auto.
  eapply checked_process_step; eassumption.
Qed.

Theorem checked_namespace_prefix (ge : genv) cell :
  (forall address fn, Genv.find_funct ge address = Some (Internal fn) ->
    checked_statement permitted (fn_body fn) = true) ->
  forall before events after,
    checked_machine permitted before -> namespace_steps ge cell before events after ->
    checked_machine permitted after.
Proof.
  intros FUNCTIONS before events after GOOD RUN; revert GOOD.
  induction RUN; intros GOOD; auto.
  apply IHRUN; eapply checked_namespace_step; eassumption.
Qed.
End SOURCE_CALLER.
