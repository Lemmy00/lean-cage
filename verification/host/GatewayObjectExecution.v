(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: SDK receipts select the same actual primitive operation. *)
From Stdlib Require Import List.
From compcert Require Import AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayRegistry GatewayMachine GatewayObjects GatewayOperations GatewayReadonly GatewayFramedRuntime.
Import ListNotations.

Theorem gateway_actual_object_operation {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    api definition arguments(property:mem->World->Prop)before world events result after next:
  gateway_object_api_definition api=Some definition ->gateway_ambient_closed backend property ->property before world ->
  gateway_steps backend ge(gateway_live(Callstate definition arguments Kstop before)world)events
    (gateway_live(Returnstate result Kstop after)next) ->
  exists prefix suffix called called_world changed changed_world observed,
    events=prefix++gateway_primitive observed::suffix /\property called called_world /\
    gateway_object_operation backend api arguments called called_world result changed changed_world observed /\
    gateway_steps backend ge(gateway_live(Callstate definition arguments Kstop before)world)prefix
      (gateway_live(Callstate definition arguments Kstop called)called_world) /\
    gateway_steps backend ge(gateway_live(Returnstate result Kstop changed)changed_world)suffix
      (gateway_live(Returnstate result Kstop after)next).
Proof.
  intros DEFINITION CLOSED GOOD RUN.
  pose proof DEFINITION as EXTERNAL;unfold gateway_object_api_definition in EXTERNAL.
  destruct(gateway_program_definition(gateway_object_api_ident api)global_definitions)as[global|]eqn:GLOBAL;[|discriminate].
  destruct global as[function|variable];[|discriminate].
  destruct function as[function|external types result_type convention];[discriminate|].
  inversion EXTERNAL;subst definition.
  destruct(gateway_external_operation_of_run backend ge _ _ _ _ _ _ _ _ _ _ _ RUN)
    as(prefix &suffix &called &called_world &changed &changed_world &observed &EVENTS &PENDING &PREFIX &OPERATION &SUFFIX).
  pose proof(gateway_pending_run_ready backend ge property CLOSED
    (Callstate(External external types result_type convention)arguments Kstop before)before world prefix called called_world
    GOOD PENDING PREFIX)as CALLED.
  exists prefix,suffix,called,called_world,changed,changed_world,observed.
  split;[exact EVENTS|]. split;[exact CALLED|]. split.
  - eexists;split;[exact DEFINITION|exact OPERATION].
  - split;assumption.
Qed.

Theorem gateway_actual_object_integer_return {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    api definition arguments(property:mem->World->Prop)before world events result after next:
  gateway_object_api_definition api=Some definition ->gateway_ambient_closed backend property ->
  (forall memory current returned changed following observed,property memory current ->
    gateway_object_operation backend api arguments memory current returned changed following observed ->
    exists status,returned=Vint status) ->property before world ->
  gateway_steps backend ge(gateway_live(Callstate definition arguments Kstop before)world)events
    (gateway_live(Returnstate result Kstop after)next) ->exists status,result=Vint status.
Proof.
  intros DEFINITION CLOSED TYPED GOOD RUN.
  destruct(gateway_actual_object_operation backend ge api definition arguments property before world events result after next DEFINITION CLOSED GOOD RUN)
    as(prefix &suffix &called &called_world &changed &changed_world &observed &EVENTS &READY &OPERATION &PREFIX &SUFFIX).
  eapply TYPED;[exact READY|exact OPERATION].
Qed.
