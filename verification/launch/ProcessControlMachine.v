(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Primitive extensions preserve the checked C statement/continuation invariant. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine LibraryMachine.
From EntryNative Require Import NativeHandoffMachine.
From EntryProcess Require Import ProcessControl ProcessMachine.

Section SOURCE_CALLER.
Variable permitted : expr -> list expr -> bool.

Definition checked_machine (state : machine) : Prop :=
  match state with live source => checked_state permitted source | dead _ => True end.

Lemma checked_machine_original (ge : genv) cell :
  (forall address fn, Genv.find_funct ge address = Some (Internal fn) ->
    checked_statement permitted (fn_body fn) = true) ->
  forall before event after, checked_machine before -> Machine.step ge cell before event after ->
    checked_machine after.
Proof.
  intros FUNCTIONS before event after GOOD STEP; inversion STEP; subst; cbn in *; auto.
  eapply checked_step; eassumption.
Qed.

Lemma checked_machine_library (ge : genv) cell :
  (forall address fn, Genv.find_funct ge address = Some (Internal fn) ->
    checked_statement permitted (fn_body fn) = true) ->
  forall before event after, checked_machine before -> library_step ge cell before event after ->
    checked_machine after.
Proof.
  intros FUNCTIONS before event after GOOD STEP; inversion STEP; subst; cbn in *; auto.
  eapply checked_machine_original; eassumption.
Qed.

Lemma checked_machine_entry (ge : genv) cell :
  (forall address fn, Genv.find_funct ge address = Some (Internal fn) ->
    checked_statement permitted (fn_body fn) = true) ->
  forall before event after, checked_machine before -> entry_handoff_step ge cell before event after ->
    checked_machine after.
Proof.
  intros FUNCTIONS before event after GOOD STEP; inversion STEP; subst; cbn in *; auto.
  eapply checked_machine_library; eassumption.
Qed.

Theorem checked_process_step (ge : genv) cell :
  (forall address fn, Genv.find_funct ge address = Some (Internal fn) ->
    checked_statement permitted (fn_body fn) = true) ->
  forall before event after, checked_machine before -> process_step ge cell before event after ->
    checked_machine after.
Proof.
  intros FUNCTIONS before event after GOOD STEP; inversion STEP; subst; cbn in *; auto.
  eapply checked_machine_entry; eassumption.
Qed.

Theorem checked_process_prefix (ge : genv) cell :
  (forall address fn, Genv.find_funct ge address = Some (Internal fn) ->
    checked_statement permitted (fn_body fn) = true) ->
  forall before events after, checked_machine before -> process_steps ge cell before events after ->
    checked_machine after.
Proof.
  intros FUNCTIONS before events after GOOD RUN; revert GOOD.
  induction RUN; intros GOOD; auto.
  apply IHRUN. eapply checked_process_step; eassumption.
Qed.
End SOURCE_CALLER.
