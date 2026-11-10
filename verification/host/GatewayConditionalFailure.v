(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: If both actual guard branches fail, an unclassified SDK
   result cannot escape that failure through a different defined Boolean evaluation. *)
From Stdlib Require Import List.
From compcert Require Import Values Memory Events Clight.
Require Import Machine.
From HostGateway Require Import GatewayMachine GatewayContexts GatewaySourceCuts GatewayFramedRuntime GatewayCallPath.
Import ListNotations.

Theorem gateway_failure_when_conditional {World Event}(backend:gateway_backend World Event)ge property
    function expression yes no continuation environment parameters memory:
  gateway_ambient_closed backend property->
  gateway_failure_when backend ge property(State function yes continuation environment parameters memory)->
  gateway_failure_when backend ge property(State function no continuation environment parameters memory)->
  gateway_failure_when backend ge property(State function(Sifthenelse expression yes no)continuation environment parameters memory).
Proof.
  intros CLOSED YES NO before world events value after next GOOD RUN.
  revert before world GOOD RUN;induction events as[|observed remaining IH];intros before world GOOD RUN.
  - inversion RUN.
  - inversion RUN as[|first event middle suffix target HEAD TAIL];subst.
    destruct(gateway_nonprimitive_step backend ge
      (State function(Sifthenelse expression yes no)continuation environment parameters before)world observed middle ltac:(cbn;tauto)HEAD)
      as[[trace[following[EVENT[REAL TARGET]]]]|[[changed[current[EVENT[INTERFERENCE TARGET]]]]|[EVENT TARGET]]];subst.
    + inversion REAL;subst;try match goal with BAD:_=_\/_=_|-_=>destruct BAD;discriminate end.
      destruct b;[eapply YES|eapply NO];[exact GOOD|exact TAIL|exact GOOD|exact TAIL].
    + eapply IH;[eapply CLOSED;eassumption|exact TAIL].
    + destruct(gateway_dead_steps _ _ _ _ _ _ TAIL)as[_ BAD];discriminate.
Qed.
