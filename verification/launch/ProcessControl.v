(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-entry.caller: Check source call restrictions under the actual Clight control semantics. *)
From Stdlib Require Import List Bool.
From compcert Require Import Coqlib Maps AST Values Memory Events Globalenvs Smallstep Ctypes Cop Clight.
Import ListNotations.

Section CALL_RESTRICTION.
Variable permitted_call : expr -> list expr -> bool.

Fixpoint checked_statement (s : statement) : bool :=
  match s with
  | Scall _ fn args => permitted_call fn args
  | Sbuiltin _ _ _ _ => false
  | Ssequence first rest | Sifthenelse _ first rest | Sloop first rest =>
      checked_statement first && checked_statement rest
  | Sswitch _ branches => checked_branches branches
  | Slabel _ body => checked_statement body
  | _ => true
  end
with checked_branches (branches : labeled_statements) : bool :=
  match branches with
  | LSnil => true
  | LScons _ body rest => checked_statement body && checked_branches rest
  end.

Fixpoint checked_continuation (k : cont) : Prop :=
  match k with
  | Kstop => True
  | Kseq body rest => checked_statement body = true /\ checked_continuation rest
  | Kloop1 first second rest | Kloop2 first second rest =>
      checked_statement first = true /\ checked_statement second = true /\
      checked_continuation rest
  | Kswitch rest => checked_continuation rest
  | Kcall _ caller _ _ rest =>
      checked_statement (fn_body caller) = true /\ checked_continuation rest
  end.

Definition checked_state (s : state) : Prop :=
  match s with
  | State fn body k _ _ _ => checked_statement (fn_body fn) = true /\
      checked_statement body = true /\ checked_continuation k
  | Callstate (Internal fn) _ k _ =>
      checked_statement (fn_body fn) = true /\ checked_continuation k
  | Callstate (External _ _ _ _) _ k _ | Returnstate _ k _ => checked_continuation k
  end.

Lemma checked_call_cont k : checked_continuation k -> checked_continuation (call_cont k).
Proof. induction k; cbn; intuition. Qed.

Lemma checked_seq_of_branches branches : checked_branches branches = true ->
  checked_statement (seq_of_labeled_statement branches) = true.
Proof.
  induction branches; cbn; auto.
  rewrite !andb_true_iff; intuition.
Qed.

Lemma checked_select_default branches : checked_branches branches = true ->
  checked_branches (select_switch_default branches) = true.
Proof.
  induction branches; cbn; auto.
  destruct o; cbn; rewrite ?andb_true_iff; intuition.
Qed.

Lemma checked_select_case n branches : checked_branches branches = true ->
  match select_switch_case n branches with
  | Some selected => checked_branches selected = true
  | None => True
  end.
Proof.
  induction branches; cbn; auto.
  rewrite andb_true_iff; intros [BODY REST].
  destruct o; cbn.
  - destruct (zeq z n); cbn.
    + rewrite andb_true_iff; auto.
    + exact (IHbranches REST).
  - exact (IHbranches REST).
Qed.

Lemma checked_select_switch n branches : checked_branches branches = true ->
  checked_branches (select_switch n branches) = true.
Proof.
  intro GOOD. unfold select_switch.
  pose proof (checked_select_case n branches GOOD) as CASE.
  destruct (select_switch_case n branches); auto.
  apply checked_select_default; exact GOOD.
Qed.

Lemma checked_find_label label body k found rest :
  checked_statement body = true -> checked_continuation k ->
  find_label label body k = Some (found, rest) ->
  checked_statement found = true /\ checked_continuation rest
with checked_find_label_branches label branches k found rest :
  checked_branches branches = true -> checked_continuation k ->
  find_label_ls label branches k = Some (found, rest) ->
  checked_statement found = true /\ checked_continuation rest.
Proof.
  - destruct body; cbn; intros GOOD CONT FOUND; try discriminate.
    + apply andb_true_iff in GOOD as [FIRST SECOND].
      destruct (find_label label body1 (Kseq body2 k)) as [[stmt next]|] eqn:FOUND1.
      * inversion FOUND; subst.
        exact (checked_find_label label body1 (Kseq body2 k) found rest
          FIRST (conj SECOND CONT) FOUND1).
      * exact (checked_find_label label body2 k found rest SECOND CONT FOUND).
    + apply andb_true_iff in GOOD as [FIRST SECOND].
      destruct (find_label label body1 k) as [[stmt next]|] eqn:FOUND1.
      * inversion FOUND; subst.
        exact (checked_find_label label body1 k found rest FIRST CONT FOUND1).
      * exact (checked_find_label label body2 k found rest SECOND CONT FOUND).
    + apply andb_true_iff in GOOD as [FIRST SECOND].
      destruct (find_label label body1 (Kloop1 body1 body2 k)) as [[stmt next]|] eqn:FOUND1.
      * inversion FOUND; subst.
        exact (checked_find_label label body1 (Kloop1 body1 body2 k) found rest
          FIRST (conj FIRST (conj SECOND CONT)) FOUND1).
      * exact (checked_find_label label body2 (Kloop2 body1 body2 k) found rest
          SECOND (conj FIRST (conj SECOND CONT)) FOUND).
    + exact (checked_find_label_branches label l (Kswitch k) found rest GOOD CONT FOUND).
    + destruct (ident_eq label l).
      * inversion FOUND; subst; auto.
      * exact (checked_find_label label body k found rest GOOD CONT FOUND).
  - destruct branches; cbn; intros GOOD CONT FOUND; try discriminate.
    apply andb_true_iff in GOOD as [BODY REST].
    destruct (find_label label s (Kseq (seq_of_labeled_statement branches) k))
      as [[stmt next]|] eqn:FOUND1.
    + inversion FOUND; subst.
      exact (checked_find_label label s (Kseq (seq_of_labeled_statement branches) k)
        found rest BODY (conj (checked_seq_of_branches branches REST) CONT) FOUND1).
    + exact (checked_find_label_branches label branches k found rest REST CONT FOUND).
Qed.

Theorem checked_step (ge : genv) :
  (forall address fn, Genv.find_funct ge address = Some (Internal fn) ->
     checked_statement (fn_body fn) = true) ->
  forall before trace after, checked_state before -> step2 ge before trace after ->
    checked_state after.
Proof.
  intros FUNCTIONS before trace after GOOD STEP.
  inversion STEP; subst; cbn in *; repeat rewrite andb_true_iff in *; try tauto.
  - destruct GOOD as [FUNCTION [CALL CONT]].
    destruct fd; cbn; auto. split; auto. eapply FUNCTIONS; eauto.
  - destruct b; cbn; tauto.
  - apply checked_call_cont; tauto.
  - apply checked_call_cont; tauto.
  - destruct GOOD as [FUNCTION [BODY CONT]]. split; [exact FUNCTION|]. split.
    + apply checked_seq_of_branches, checked_select_switch; exact BODY.
    + exact CONT.
  - destruct GOOD as [FUNCTION [BODY CONT]].
    destruct (checked_find_label _ _ _ _ _ FUNCTION (checked_call_cont _ CONT) H)
      as [FOUND NEXT]. auto.
Qed.

Theorem checked_execution_prefix (ge : genv) :
  (forall address fn, Genv.find_funct ge address = Some (Internal fn) ->
     checked_statement (fn_body fn) = true) ->
  forall before trace after, checked_state before -> star step2 ge before trace after ->
    checked_state after.
Proof.
  intros FUNCTIONS before trace after GOOD RUN. revert GOOD.
  induction RUN; intros GOOD; auto.
  apply IHRUN. eapply checked_step; eauto.
Qed.
End CALL_RESTRICTION.
