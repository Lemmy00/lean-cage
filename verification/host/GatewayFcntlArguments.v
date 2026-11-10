(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Real typed argument evaluation retains the fixed fcntl command. *)
From Stdlib Require Import ZArith List Bool.
From compcert Require Import Coqlib Maps Integers AST Values Memory Globalenvs Ctypes Ctypesdefs Cop Clight.
From HostGateway Require Import GatewayFcntlProfile GatewayFcntlControl.
Import ListNotations.

Lemma gateway_fcntl_command_constants command : gateway_fcntl_command command = true ->
  command = Int.repr 3 \/ command = Int.repr 4 \/ command = Int.repr 1030.
Proof.
  unfold gateway_fcntl_command; rewrite !orb_true_iff; intros [[FIRST |SECOND] |THIRD].
  - left; apply Int.same_if_eq; exact FIRST.
  - right; left; apply Int.same_if_eq; exact SECOND.
  - right; right; apply Int.same_if_eq; exact THIRD.
Qed.

Theorem gateway_fcntl_evaluated_command ge environment temporaries memory destination callee arguments values :
  gateway_fcntl_statement (Scall destination callee arguments) = true ->
  classify_fun (typeof callee) = fun_case_f [tint; tint; tint] tint cc_default ->
  eval_exprlist ge environment temporaries memory arguments [tint; tint; tint] values ->
  gateway_fcntl_values values.
Proof.
  intros SCOPED TYPE EVALUATED.
  inversion EVALUATED as [|first firstTail firstType firstTypes firstValue firstCast firstValues FIRST FIRST_CAST MORE1]; subst.
  inversion MORE1 as [|second secondTail secondType secondTypes secondValue secondCast secondValues SECOND SECOND_CAST MORE2]; subst.
  inversion MORE2 as [|last lastTail lastType lastTypes lastValue lastCast lastValues LAST LAST_CAST MORE3]; subst.
  inversion MORE3; subst.
  cbn [gateway_fcntl_statement gateway_fcntl_local] in SCOPED.
  unfold gateway_fcntl_shape in SCOPED; rewrite TYPE in SCOPED; cbn in SCOPED.
  destruct second; try discriminate.
  match goal with
  | GOOD : context[type_eq ?ty tint] |- _ => destruct (type_eq ty tint) as [SAME |DIFFERENT];
      [subst ty |discriminate]
  end.
  apply andb_true_iff in SCOPED as [COMMAND TRIVIAL].
  inversion SECOND; subst; try match goal with BAD : eval_lvalue _ _ _ _ (Econst_int _ _) _ _ _ |- _ => inversion BAD end.
  destruct (gateway_fcntl_command_constants _ COMMAND) as [SAME |[SAME |SAME]]; subst;
    vm_compute in SECOND_CAST; inversion SECOND_CAST; subst.
  all: unfold gateway_fcntl_values; eexists; eexists; eexists; split; [reflexivity |auto].
Qed.
