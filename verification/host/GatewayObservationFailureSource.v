(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual metadata key errors cannot become a successful missing observation. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayOutcome GatewayOutcomeConstruction
  GatewaySourceBoundCalls GatewaySourceSegmentAutomation GatewaySourcePaths GatewaySourceCuts GatewayFramedRuntime
  GatewayOutcomeGetterSource GatewayUnaryExpressions GatewayFailurePaths GatewayValueReturns GatewayNoLocalEntry GatewayFunctionEntry GatewayCalls.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_observation_null_key_source {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    parameters before:
  gateway_failure_when backend ge(fun _ _=>True)
    (Returnstate Vnullptr(gateway_observation_key_cont parameters)before).
Proof.
  assert(CLOSED:gateway_ambient_closed backend(fun _ _=>True))by(unfold gateway_ambient_closed;intros;exact I).
  assert(POINTER_RETURN:gateway_pointer_return f_host_outcome_observation)by(repeat eexists).
  gateway_bound_source_failure CLOSED
    ltac:(fun _=>eapply gateway_unary_expression_value with(value:=Vnullptr)(result:=Vint Int.one);
      [gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|reflexivity])
    ltac:(fun _=>reflexivity)POINTER_RETURN.
Qed.

Theorem gateway_actual_observation_failed_key_returns_null {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    parameters before world events value after next:
  gateway_steps backend ge
    (gateway_live(Returnstate Vnullptr(gateway_observation_key_cont parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value=Vnullptr.
Proof.
  intro RUN;exact(gateway_observation_null_key_source backend ge parameters before
    before world events value after next I RUN).
Qed.
