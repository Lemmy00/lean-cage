(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces: Actual nonzero helper/signal tests cannot return readiness success. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewayMachine GatewaySource GatewayReadySource GatewayReturns
  GatewayControlPaths GatewayReturnTypes.
Import ListNotations.

Definition gateway_failure_return := Sreturn (Some (Eunop Oneg (Econst_int Int.one tint) tint)).
Definition gateway_int_test identifier := Sifthenelse (Etempvar identifier tint) gateway_failure_return Sskip.

Lemma actual_ready_control_test : ready_control_test = gateway_int_test _t'1.
Proof. reflexivity. Qed.

Lemma gateway_nonzero_test_failure ge function identifier continuation environment temporaries memory status :
  fn_return function = tint -> call_cont continuation = Kstop ->
  temporaries ! identifier = Some (Vint status) -> status <> Int.zero ->
  gateway_constant_path ge (Vint (Int.neg Int.one))
    (State function (gateway_int_test identifier) continuation environment temporaries memory).
Proof.
  intros TYPE CONTINUATION LOOK NONZERO.
  eapply gateway_constant_next with (next := State function gateway_failure_return continuation environment temporaries memory).
  - cbn; tauto.
  - intro another; apply certified_if_edge with (v := Vint status) (b := true).
    + apply old_expression_value, value_temp; exact LOOK.
    + change (Some (negb (Int.eq status Int.zero)) = Some true).
      rewrite (Int.eq_false status Int.zero NONZERO); reflexivity.
  - eapply gateway_constant_at_return with (value := Vint (Int.neg Int.one)).
    + exact CONTINUATION.
    + intro another; apply old_expression_value; eapply value_unary; [constructor | reflexivity].
    + intro another; rewrite TYPE; reflexivity.
Qed.

Lemma gateway_undefined_test_blocked ge function identifier continuation environment temporaries memory :
  temporaries ! identifier = Some Vundef ->
  gateway_blocked_path ge (State function (gateway_int_test identifier) continuation environment temporaries memory).
Proof.
  intro LOOK; apply gateway_blocked_at.
  - cbn; tauto.
  - intros; discriminate.
  - intros another trace target STEP; inversion STEP; subst;
      try match goal with BAD : _ = _ \/ _ = _ |- _ => destruct BAD; discriminate end.
    match goal with VALUE : eval_expr _ _ _ _ (Etempvar identifier tint) _ |- _ =>
      pose proof (evaluated_unique _ _ _ _ _ _ (value_temp _ _ _ _ _ tint Vundef LOOK) _ VALUE) as SAME; subst end.
    cbn [typeof bool_val] in *; discriminate.
    all: try match goal with LOCATION : eval_lvalue _ _ _ _ (Etempvar _ _) _ _ _ |- _ => inversion LOCATION end.
Qed.

Theorem gateway_successful_int_test_zero {World Event} (backend : gateway_backend World Event) ge
    function identifier continuation environment temporaries before world events status after next :
  fn_return function = tint -> call_cont continuation = Kstop ->
  temporaries ! identifier = Some (Vint status) ->
  gateway_steps backend ge
    (gateway_live (State function (gateway_int_test identifier) continuation environment temporaries before) world)
    events (gateway_live (Returnstate (Vint Int.zero) Kstop after) next) -> status = Int.zero.
Proof.
  intros TYPE CONTINUATION LOOK RUN; destruct (Int.eq_dec status Int.zero) as [SAME | DIFFERENT]; [exact SAME |].
  pose proof (gateway_constant_path_actual backend ge _ _ world events _ after next
    (gateway_nonzero_test_failure ge function identifier continuation environment temporaries before status
      TYPE CONTINUATION LOOK DIFFERENT) RUN) as BAD; discriminate BAD.
Qed.

Theorem gateway_successful_helper_test_zero {World Event} (backend : gateway_backend World Event) ge
    function identifier continuation environment temporaries before world events value after next :
  fn_return function = tint -> call_cont continuation = Kstop ->
  temporaries ! identifier = Some value -> gateway_int_return_value value ->
  gateway_steps backend ge
    (gateway_live (State function (gateway_int_test identifier) continuation environment temporaries before) world)
    events (gateway_live (Returnstate (Vint Int.zero) Kstop after) next) -> value = Vint Int.zero.
Proof.
  intros TYPE CONTINUATION LOOK [UNDEFINED | [ZERO | NEGATIVE]] RUN; subst value.
  - exfalso; eapply gateway_blocked_cannot_return; [eapply gateway_undefined_test_blocked; exact LOOK | exact RUN].
  - reflexivity.
  - pose proof (gateway_successful_int_test_zero backend ge function identifier continuation environment temporaries
      before world events (Int.neg Int.one) after next TYPE CONTINUATION LOOK RUN) as BAD; discriminate BAD.
Qed.
