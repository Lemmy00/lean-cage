(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: A selected SDK return is the same actual primitive occurrence. *)
From Stdlib Require Import List Lia.
From compcert Require Import AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayRegistry GatewayMachine GatewayObjects GatewayContexts
  GatewayOperations GatewayFramedRuntime GatewaySourcePaths GatewayExternalFrontier.
Import ListNotations.

Theorem gateway_source_object_receipt {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    api definition arguments continuation(property:mem->World->Prop)source
    before world events value after next:
  gateway_object_api_definition api=Some definition->is_call_cont continuation->
  (0<gateway_cont_weight continuation)%nat->gateway_ambient_closed backend property->
  gateway_source_path backend ge definition arguments continuation property source property->
  property before world->
  gateway_steps backend ge(gateway_live(gateway_replace_memory source before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists prefix suffix called called_world returned changed changed_world observed,
    events=prefix++gateway_primitive observed::suffix /\property called called_world /\
    gateway_steps backend ge(gateway_live(gateway_replace_memory source before)world)prefix
      (gateway_live(Callstate definition arguments continuation called)called_world) /\
    gateway_object_operation backend api arguments called called_world returned changed changed_world observed /\
    gateway_steps backend ge(gateway_live(Returnstate returned continuation changed)changed_world)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros DEFINITION CALL WEIGHT CLOSED PATH INPUT RUN.
  destruct(gateway_source_path_cut backend ge definition arguments continuation property source property PATH
    before world events value after next INPUT RUN)
    as(prelude &rest &at_call &owner &EVENTS &QUIET &PRELUDE &READY &REST).
  pose proof DEFINITION as EXTERNAL;unfold gateway_object_api_definition in EXTERNAL.
  destruct(gateway_program_definition(gateway_object_api_ident api)global_definitions)as[global|]eqn:GLOBAL;
    [|discriminate].
  destruct global as[function|variable];[|discriminate].
  destruct function as[function|external types result_type convention];[discriminate|].
  inversion EXTERNAL;subst definition.
  destruct(gateway_actual_external_frontier backend ge external types result_type convention arguments continuation
    at_call owner rest value after next CALL WEIGHT REST)
    as(pending &suffix &called &called_world &returned &changed &changed_world &observed &TAIL &PENDING &PREFIX &OPERATION &SUFFIX).
  assert(CALLED:property called called_world).
  { eapply(gateway_pending_run_ready backend ge property CLOSED
      (Callstate(External external types result_type convention)arguments continuation at_call)
      at_call owner pending called called_world READY PENDING PREFIX). }
  exists(prelude++pending),suffix,called,called_world,returned,changed,changed_world,observed.
  split;[rewrite EVENTS,TAIL,<-app_assoc;reflexivity|]. split;[exact CALLED|]. split.
  - eapply gateway_steps_append;eassumption.
  - split;[eexists;split;[exact DEFINITION|exact OPERATION]|exact SUFFIX].
Qed.
