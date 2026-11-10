(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Actual C goto/switch continuations retain source pointer scopes. *)
From Stdlib Require Import List Bool.
From compcert Require Import Coqlib AST Values Ctypes Clight.
From HostGateway Require Import GatewayPointerControl GatewayGlobalAddresses.

Lemma gateway_pointer_find_label private label body continuation found rest :
  gateway_pointer_statement body = true -> gateway_pointer_cont private continuation ->
  find_label label body continuation = Some (found, rest) ->
  gateway_pointer_statement found = true /\ gateway_pointer_cont private rest
with gateway_pointer_find_label_branches private label branches continuation found rest :
  gateway_pointer_branches branches = true -> gateway_pointer_cont private continuation ->
  find_label_ls label branches continuation = Some (found, rest) ->
  gateway_pointer_statement found = true /\ gateway_pointer_cont private rest.
Proof.
  - destruct body; cbn [find_label gateway_pointer_statement gateway_statement_addresses];
      intros SCOPED CONTINUATION FOUND; try discriminate.
    all: repeat rewrite andb_true_iff in SCOPED.
    + destruct SCOPED as [TRIVIAL [FIRST SECOND]].
      destruct (find_label label body1 (Kseq body2 continuation)) as [[statement next] |] eqn:LEFT.
      * inversion FOUND; subst; eapply gateway_pointer_find_label with (continuation := Kseq body2 continuation);
          [exact FIRST |split; [exact SECOND |exact CONTINUATION] |exact LEFT].
      * eapply gateway_pointer_find_label with (continuation := continuation); [exact SECOND |exact CONTINUATION |exact FOUND].
    + destruct SCOPED as [EXPRESSION [FIRST SECOND]].
      destruct (find_label label body1 continuation) as [[statement next] |] eqn:LEFT.
      * inversion FOUND; subst; eapply gateway_pointer_find_label with (continuation := continuation); [exact FIRST |exact CONTINUATION |exact LEFT].
      * eapply gateway_pointer_find_label with (continuation := continuation); [exact SECOND |exact CONTINUATION |exact FOUND].
    + destruct SCOPED as [TRIVIAL [FIRST SECOND]].
      destruct (find_label label body1 (Kloop1 body1 body2 continuation)) as [[statement next] |] eqn:LEFT.
      * inversion FOUND; subst; eapply gateway_pointer_find_label with (continuation := Kloop1 body1 body2 continuation);
          [exact FIRST |repeat split; assumption |exact LEFT].
      * eapply gateway_pointer_find_label with (continuation := Kloop2 body1 body2 continuation);
          [exact SECOND |repeat split; assumption |exact FOUND].
    + eapply gateway_pointer_find_label_branches with (continuation := Kswitch continuation);
        [exact (proj2 SCOPED) |exact CONTINUATION |exact FOUND].
    + destruct (ident_eq label l).
      * inversion FOUND; subst; split; [exact (proj2 SCOPED) |exact CONTINUATION].
      * eapply gateway_pointer_find_label with (continuation := continuation); [exact (proj2 SCOPED) |exact CONTINUATION |exact FOUND].
  - destruct branches; cbn [find_label_ls gateway_pointer_branches]; intros SCOPED CONTINUATION FOUND; try discriminate.
    apply andb_true_iff in SCOPED as [FIRST REST].
    destruct (find_label label s (Kseq (seq_of_labeled_statement branches) continuation))
      as [[statement next] |] eqn:LEFT.
    + inversion FOUND; subst; eapply gateway_pointer_find_label with
        (continuation := Kseq (seq_of_labeled_statement branches) continuation);
        [exact FIRST |split; [apply gateway_pointer_switch_sequence; exact REST |exact CONTINUATION] |exact LEFT].
    + eapply gateway_pointer_find_label_branches with (continuation := continuation); [exact REST |exact CONTINUATION |exact FOUND].
Qed.
