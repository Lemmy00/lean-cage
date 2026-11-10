(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A failed native Outcome allocation cannot produce a successful result. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Ctypes Ctypesdefs Cop Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess CallAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayOutcomeConstruction GatewaySourceCuts
  GatewaySourceDynamic GatewayFailurePaths GatewayFramedRuntime GatewayUnaryExpressions.

Theorem gateway_actual_outcome_allocation_failure {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    environment parameters before world events value after next:
  gateway_steps backend ge
    (gateway_live(Returnstate Vnullptr(gateway_outcome_allocation_cont environment parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value=Vnullptr.
Proof.
  intro RUN.
  assert(CLOSED:gateway_ambient_closed backend(fun _ _=>True))by(unfold gateway_ambient_closed;intros;exact I).
  assert(TYPE:gateway_pointer_return f_host_outcome_from)by(eexists;eexists;reflexivity).
  assert(PATH:gateway_failure_when backend ge(fun _ _=>True)
    (Returnstate Vnullptr(gateway_outcome_allocation_cont environment parameters)before)).
  { gateway_source_dynamic_failure CLOSED
      ltac:(fun _=>lazymatch goal with
        |-expression_value _ _ _ _ (Eunop _ _ _) _=>
          eapply gateway_unary_expression_value with(value:=Vnullptr)(result:=Vint Int.one);
            [gateway_source_dynamic_expression ltac:(fun _=>fail)ltac:(fun _=>reflexivity)|reflexivity]
        end)ltac:(fun _=>reflexivity)TYPE. }
  exact(PATH before world events value after next I RUN).
Qed.
