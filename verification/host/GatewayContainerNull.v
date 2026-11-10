(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Failed container allocation reaches the actual null return. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContainerAllocation GatewayContainerLength GatewayValueGuards
  GatewaySourceCuts GatewaySourceDynamic GatewayFailurePaths GatewayFramedRuntime GatewayUnaryExpressions.

Theorem gateway_actual_container_allocation_failure {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    container slots parameters before world events value after next:
  gateway_steps backend ge
    (gateway_live(Returnstate Vnullptr(gateway_container_constructor_cont container slots parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value=Vnullptr.
Proof.
  intro RUN.
  assert(CLOSED:gateway_ambient_closed backend(fun _ _=>True))by(unfold gateway_ambient_closed;intros;exact I).
  assert(PATH:gateway_failure_when backend ge(fun _ _=>True)
    (Returnstate Vnullptr(gateway_container_constructor_cont container slots parameters)before)).
  { destruct container;gateway_source_dynamic_failure CLOSED
      ltac:(fun _=>lazymatch goal with
        |-expression_value _ _ _ _ (Eunop _ _ _) _=>
          eapply gateway_unary_expression_value with(value:=Vnullptr)(result:=Vint Int.one);
            [gateway_source_dynamic_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|reflexivity]
        end)ltac:(fun _=>reflexivity)gateway_value_pointer_return. }
  exact(PATH before world events value after next I RUN).
Qed.
