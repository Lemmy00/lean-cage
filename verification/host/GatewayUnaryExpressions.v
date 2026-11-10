(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Unary source checks use actual typed expression evaluations. *)
From compcert Require Import Values Memory Ctypes Cop Clight.
Require Import LocalAccess.

Lemma gateway_unary_expression_value ge environment parameters memory operation expression ty value result :
  expression_value ge environment parameters memory expression value ->
  sem_unary_operation operation value(typeof expression)memory=Some result ->
  expression_value ge environment parameters memory(Eunop operation expression ty)result.
Proof.
  intros[REAL UNIQUE]OPERATION;split;[econstructor;eassumption|].
  intros other EVALUATED;inversion EVALUATED;subst.
  - match goal with VALUE:eval_expr _ _ _ _ expression _|-_=>pose proof(UNIQUE _ VALUE)as SAME;subst end;congruence.
  - match goal with LOCATION:eval_lvalue _ _ _ _(Eunop _ _ _)_ _ _|-_=>inversion LOCATION end.
Qed.
