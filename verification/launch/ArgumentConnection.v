(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: State the exact imported bounds; the native memory/caller producer is separate. *)
From Stdlib Require Import Arith List Lia.
From LeanImport Require Import Lean.
Require Import ArgumentsImport.
Local Close Scope lean_scope.
Local Open Scope nat_scope.

Lemma argument_ite_true (A : Type) (p : SProp) (d : Decidable p) (yes no : A) (h : p) :
  ite A p d yes no = yes.
Proof. destruct d as [b reflect]; destruct b; [destruct (reflect h)|reflexivity]. Qed.
Lemma argument_ite_false (A : Type) (p : SProp) (d : Decidable p) (yes no : A) (h : Not p) :
  ite A p d yes no = no.
Proof. destruct d as [b reflect]; destruct b; [reflexivity|destruct (h reflect)]. Qed.

Ltac argument_branch hypothesis :=
  lazymatch type of hypothesis with
  | ite ?A ?condition ?decision ?yes ?no = ?target =>
      let decider := fresh "decider" in
      let equation := fresh "decision_equation" in
      let bit := fresh "bit" in
      let reflects := fresh "reflects" in
      remember decision as decider eqn:equation;
      clear equation;
      destruct decider as [bit reflects]; destruct bit;
      [rewrite (argument_ite_false A condition _ yes no reflects) in hypothesis
      |rewrite (argument_ite_true A condition _ yes no reflects) in hypothesis]
  end.

Theorem imported_digit_bound limit initial byte value :
  LeanCage_Entry_Arguments_digit limit initial byte = Option_some_inst1 Nat value ->
  Nat_le value limit.
Proof.
  intro RUN; unfold LeanCage_Entry_Arguments_digit in RUN.
  argument_branch RUN.
  - cbn zeta in RUN; argument_branch RUN.
    + discriminate.
    + injection RUN as SAME; subst value; assumption.
  - discriminate.
Qed.

Theorem imported_digits_bound limit initial bytes value :
  Nat_le initial limit ->
  LeanCage_Entry_Arguments_digits limit initial bytes = Option_some_inst1 Nat value ->
  Nat_le value limit.
Proof.
  revert initial; induction bytes as [|byte rest IH]; intros initial START RUN.
  - change (Option_some_inst1 Nat initial = Option_some_inst1 Nat value) in RUN.
    injection RUN as SAME; subst value; exact START.
  - change (match LeanCage_Entry_Arguments_digit limit initial byte with
      | Option_none_inst1 _ => Option_none_inst1 Nat
      | Option_some_inst1 _ next => LeanCage_Entry_Arguments_digits limit next rest
      end = Option_some_inst1 Nat value) in RUN.
    destruct (LeanCage_Entry_Arguments_digit limit initial byte) as [|next] eqn:STEP.
    + discriminate.
    + eapply IH; [apply imported_digit_bound with (initial:=initial)(byte:=byte);exact STEP|exact RUN].
Qed.

Theorem imported_unsigned_bound limit value bytes :
  Lean.eq (LeanCage_Entry_Arguments_unsigned limit bytes) (Option_some_inst1 Nat value) ->
  Nat_le value limit.
Proof.
  intro EQ; assert (RUN : LeanCage_Entry_Arguments_unsigned limit bytes = Option_some_inst1 Nat value).
  { destruct EQ; reflexivity. }
  destruct bytes as [|first rest].
  - discriminate RUN.
  - unfold LeanCage_Entry_Arguments_unsigned in RUN.
    cbn [LeanCage_Entry_Arguments_digits_match_1 List_casesOn_inst2 List_inst1_recl] in RUN.
    argument_branch RUN.
    + eapply imported_digits_bound with (initial:=Nat_zero).
      * apply nat_le_Nat_le; change (0 <= nat_of_Nat limit); lia.
      * exact RUN.
    + discriminate.
Qed.

Definition unsigned_bound_checked_type :
  forall (limit value : Nat) (bytes : List_inst1 UInt8),
    Lean.eq (LeanCage_Entry_Arguments_unsigned limit bytes) (Option_some_inst1 Nat value) ->
    Nat_le value limit := imported_unsigned_bound.
