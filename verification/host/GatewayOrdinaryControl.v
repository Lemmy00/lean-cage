(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller.initialization: Source control retains ordinary call and write restrictions. *)
From Stdlib Require Import List Bool.
From compcert Require Import Coqlib Maps AST Values Memory Events Globalenvs Ctypes Cop Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayRegistry GatewayMachine GatewayLinkedSource
  GatewayOrdinarySource.
Import ListNotations.

Theorem gateway_ordinary_switch_sequence branches :
  gateway_ordinary_branches branches = true ->
  gateway_ordinary_statement (seq_of_labeled_statement branches) = true.
Proof.
  induction branches; cbn [gateway_ordinary_branches seq_of_labeled_statement gateway_ordinary_statement gateway_ordinary_action];
    intro SAFE; [reflexivity |].
  apply andb_true_iff in SAFE as [FIRST REST]; rewrite FIRST, (IHbranches REST); reflexivity.
Qed.

Theorem gateway_ordinary_switch_default branches :
  gateway_ordinary_branches branches = true -> gateway_ordinary_branches (select_switch_default branches) = true.
Proof.
  induction branches as [|label body rest IH]; [intro; reflexivity |].
  intro SAFE; destruct label; cbn [select_switch_default]; [apply IH |exact SAFE].
  exact (proj2 (proj1 (andb_true_iff _ _) SAFE)).
Qed.

Theorem gateway_ordinary_switch_case selector branches selected :
  gateway_ordinary_branches branches = true -> select_switch_case selector branches = Some selected ->
  gateway_ordinary_branches selected = true.
Proof.
  revert selected; induction branches as [|label body rest IH]; intros selected SAFE FOUND; [discriminate |].
  cbn [select_switch_case] in FOUND; destruct label.
  - destruct (zeq z selector); [inversion FOUND; subst; exact SAFE |].
    eapply IH; [exact (proj2 (proj1 (andb_true_iff _ _) SAFE)) |exact FOUND].
  - eapply IH; [exact (proj2 (proj1 (andb_true_iff _ _) SAFE)) |exact FOUND].
Qed.

Theorem gateway_ordinary_switch selector branches :
  gateway_ordinary_branches branches = true -> gateway_ordinary_statement
    (seq_of_labeled_statement (select_switch selector branches)) = true.
Proof.
  intro SAFE; apply gateway_ordinary_switch_sequence; unfold select_switch.
  destruct (select_switch_case selector branches) as [selected |] eqn:SELECT.
  - eapply gateway_ordinary_switch_case; eassumption.
  - apply gateway_ordinary_switch_default; exact SAFE.
Qed.

Fixpoint gateway_ordinary_cont (continuation : cont) : Prop :=
  match continuation with
  | Kstop => True
  | Kseq body rest => gateway_ordinary_statement body = true /\ gateway_ordinary_cont rest
  | Kloop1 first second rest | Kloop2 first second rest =>
      gateway_ordinary_statement first = true /\ gateway_ordinary_statement second = true /\ gateway_ordinary_cont rest
  | Kswitch rest => gateway_ordinary_cont rest
  | Kcall _ body environment _ rest => gateway_ordinary_statement (fn_body body) = true /\
      gateway_global_names_unshadowed environment /\ gateway_ordinary_cont rest
  end.

Theorem gateway_ordinary_call_cont continuation :
  gateway_ordinary_cont continuation -> gateway_ordinary_cont (call_cont continuation).
Proof. induction continuation; cbn; tauto. Qed.

Definition gateway_ordinary_entry_scope definition : Prop :=
  match definition with
  | Internal body => gateway_ordinary_function body = true /\
      exists identifier, In (identifier, Gfun (Internal body)) global_definitions
  | External _ _ _ _ => True
  end.

Definition gateway_ordinary_source source : Prop :=
  match source with
  | State body current continuation environment _ _ =>
      gateway_ordinary_statement (fn_body body) = true /\ gateway_ordinary_statement current = true /\
      gateway_ordinary_cont continuation /\ gateway_global_names_unshadowed environment
  | Callstate definition _ continuation _ => gateway_ordinary_entry_scope definition /\ gateway_ordinary_cont continuation
  | Returnstate _ continuation _ => gateway_ordinary_cont continuation
  end.

Lemma gateway_ordinary_find_label label body continuation found rest :
  gateway_ordinary_statement body = true -> gateway_ordinary_cont continuation ->
  find_label label body continuation = Some (found, rest) ->
  gateway_ordinary_statement found = true /\ gateway_ordinary_cont rest
with gateway_ordinary_find_label_branches label branches continuation found rest :
  gateway_ordinary_branches branches = true -> gateway_ordinary_cont continuation ->
  find_label_ls label branches continuation = Some (found, rest) ->
  gateway_ordinary_statement found = true /\ gateway_ordinary_cont rest.
Proof.
  - destruct body; cbn [find_label gateway_ordinary_statement gateway_ordinary_action];
      intros SCOPED CONTINUATION FOUND; try discriminate.
    all: repeat rewrite andb_true_iff in SCOPED.
    + destruct SCOPED as [TRIVIAL [FIRST SECOND]].
      destruct (find_label label body1 (Kseq body2 continuation)) as [[statement next] |] eqn:LEFT.
      * inversion FOUND; subst; eapply gateway_ordinary_find_label with (continuation := Kseq body2 continuation);
          [exact FIRST |split; [exact SECOND |exact CONTINUATION] |exact LEFT].
      * eapply gateway_ordinary_find_label with (continuation := continuation); [exact SECOND |exact CONTINUATION |exact FOUND].
    + destruct SCOPED as [EXPRESSION [FIRST SECOND]].
      destruct (find_label label body1 continuation) as [[statement next] |] eqn:LEFT.
      * inversion FOUND; subst; eapply gateway_ordinary_find_label with (continuation := continuation); [exact FIRST |exact CONTINUATION |exact LEFT].
      * eapply gateway_ordinary_find_label with (continuation := continuation); [exact SECOND |exact CONTINUATION |exact FOUND].
    + destruct SCOPED as [TRIVIAL [FIRST SECOND]].
      destruct (find_label label body1 (Kloop1 body1 body2 continuation)) as [[statement next] |] eqn:LEFT.
      * inversion FOUND; subst; eapply gateway_ordinary_find_label with (continuation := Kloop1 body1 body2 continuation);
          [exact FIRST |repeat split; assumption |exact LEFT].
      * eapply gateway_ordinary_find_label with (continuation := Kloop2 body1 body2 continuation);
          [exact SECOND |repeat split; assumption |exact FOUND].
    + eapply gateway_ordinary_find_label_branches with (continuation := Kswitch continuation);
        [exact (proj2 SCOPED) |exact CONTINUATION |exact FOUND].
    + destruct (ident_eq label l).
      * inversion FOUND; subst; split; [exact (proj2 SCOPED) |exact CONTINUATION].
      * eapply gateway_ordinary_find_label with (continuation := continuation); [exact (proj2 SCOPED) |exact CONTINUATION |exact FOUND].
  - destruct branches; cbn [find_label_ls gateway_ordinary_branches]; intros SCOPED CONTINUATION FOUND; try discriminate.
    apply andb_true_iff in SCOPED as [FIRST REST].
    destruct (find_label label s (Kseq (seq_of_labeled_statement branches) continuation))
      as [[statement next] |] eqn:LEFT.
    + inversion FOUND; subst; eapply gateway_ordinary_find_label with
        (continuation := Kseq (seq_of_labeled_statement branches) continuation);
        [exact FIRST |split; [apply gateway_ordinary_switch_sequence; exact REST |exact CONTINUATION] |exact LEFT].
    + eapply gateway_ordinary_find_label_branches with (continuation := continuation); [exact REST |exact CONTINUATION |exact FOUND].
Qed.
