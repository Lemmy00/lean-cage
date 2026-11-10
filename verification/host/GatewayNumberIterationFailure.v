(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Failed chunk arithmetic cannot be turned into a returned
   number by later ignored releases, callbacks, memory changes or interrupted execution. *)
From Stdlib Require Import List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayNumberIntegerStructure GatewayNumberIntegerCalls GatewayNumberFloatSource
  GatewaySourceCuts GatewaySourcePaths GatewaySourceBoundCalls GatewaySourceSegmentAutomation GatewayUnaryExpressions GatewayFramedRuntime
  GatewayFailurePaths GatewayNumberFailures GatewayValueReturns GatewayContexts.
Import ListNotations.

Theorem gateway_number_null_part_denied {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)parameters memory:
  gateway_failure_result backend ge(Returnstate Vnullptr(number_integer_part_cont parameters)memory).
Proof.
  assert(CLOSED:gateway_ambient_closed backend(fun _ _=>True))by(unfold gateway_ambient_closed;intros;exact I).
  assert(FAILURE:gateway_failure_when backend ge(fun _ _=>True)(Returnstate Vnullptr(number_integer_part_cont parameters)memory)).
  { gateway_bound_source_failure CLOSED
      ltac:(fun _=>eapply gateway_unary_expression_value with(value:=Vnullptr)(result:=Vint Int.one);
        [gateway_segment_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|reflexivity])
      ltac:(fun _=>reflexivity)gateway_number_float_pointer_return. }
  intros before world events value after next RUN;exact(FAILURE before world events value after next I RUN).
Qed.

Theorem gateway_number_null_scaled_denied {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)parameters ignored memory:
  parameters!_scaled=Some Vnullptr->
  gateway_failure_result backend ge(Returnstate ignored(number_integer_release_value_cont parameters)memory).
Proof.
  intro NULL.
  assert(CLOSED:gateway_ambient_closed backend(fun _ _=>True))by(unfold gateway_ambient_closed;intros;exact I).
  assert(FAILURE:gateway_failure_when backend ge(fun _ _=>True)(Returnstate ignored(number_integer_release_value_cont parameters)memory)).
  { gateway_bound_source_failure CLOSED
      ltac:(fun _=>eapply gateway_unary_expression_value with(value:=Vnullptr)(result:=Vint Int.one);
        [apply old_expression_value,value_temp;exact NULL|reflexivity])
      ltac:(fun _=>reflexivity)gateway_number_float_pointer_return. }
  intros before world events value after next RUN;exact(FAILURE before world events value after next I RUN).
Qed.

Theorem gateway_number_null_sum_denied {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)parameters ignored memory:
  parameters!_value__1=Some Vnullptr->
  gateway_failure_result backend ge(Returnstate ignored(number_integer_release_part_cont parameters)memory).
Proof.
  intro NULL.
  assert(CLOSED:gateway_ambient_closed backend(fun _ _=>True))by(unfold gateway_ambient_closed;intros;exact I).
  assert(FAILURE:gateway_failure_when backend ge(fun _ _=>True)(Returnstate ignored(number_integer_release_part_cont parameters)memory)).
  { gateway_bound_source_failure CLOSED
      ltac:(fun _=>eapply gateway_unary_expression_value with(value:=Vnullptr)(result:=Vint Int.one);
        [apply old_expression_value,value_temp;exact NULL|reflexivity])
      ltac:(fun _=>reflexivity)gateway_number_float_pointer_return. }
  intros before world events value after next RUN;exact(FAILURE before world events value after next I RUN).
Qed.
