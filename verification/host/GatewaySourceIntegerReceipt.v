(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: A real source-selected SDK call supplies its actual typed return. *)
From Stdlib Require Import List Lia.
From compcert Require Import AST Integers Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewaySourcePaths GatewayFramedRuntime
  GatewayObjects GatewayObjectExecution.
Import ListNotations.

Theorem gateway_source_integer_receipt {World Event} (backend : gateway_backend World Event) (ge : Clight.genv)
    api definition arguments continuation (property boundary : mem -> World -> Prop) source
    before world events value after next :
  gateway_object_api_definition api = Some definition -> is_call_cont continuation ->
  (0 < gateway_cont_weight continuation)%nat ->
  gateway_source_path backend ge definition arguments continuation property source boundary ->
  gateway_ambient_closed backend boundary ->
  (forall memory current returned changed following observed, boundary memory current ->
    gateway_object_operation backend api arguments memory current returned changed following observed ->
    exists status, returned = Vint status) ->
  property before world ->
  gateway_steps backend ge (gateway_live (gateway_replace_memory source before) world) events
    (gateway_live (Returnstate value Kstop after) next) ->
  exists prefix operation suffix called called_world changed changed_world status,
    events = prefix ++ operation ++ suffix /\
    Forall (fun event => event = gateway_source E0 \/ event = gateway_ambient) prefix /\
    gateway_steps backend ge (gateway_live (gateway_replace_memory source before) world) prefix
      (gateway_live (Callstate definition arguments continuation called) called_world) /\
    boundary called called_world /\
    gateway_steps backend ge (gateway_live (Callstate definition arguments Kstop called) called_world) operation
      (gateway_live (Returnstate (Vint status) Kstop changed) changed_world) /\
    gateway_steps backend ge (gateway_live (Returnstate (Vint status) continuation changed) changed_world) suffix
      (gateway_live (Returnstate value Kstop after) next).
Proof.
  intros DEFINITION CALL POSITIVE PATH CLOSED TYPED INPUT RUN.
  destruct (gateway_source_path_cut backend ge definition arguments continuation property source boundary PATH
    before world events value after next INPUT RUN)
    as (prefix & rest & called & called_world & EVENTS & QUIET & PREFIX & READY & FROM_CALL).
  destruct (gateway_return_cut backend ge definition arguments continuation called called_world rest
    (Returnstate value Kstop after) next CALL POSITIVE FROM_CALL)
    as (operation & suffix & returned & changed & changed_world & REST_EVENTS & OPERATION & REST).
  destruct (gateway_actual_object_integer_return backend ge api definition arguments boundary
    called called_world operation returned changed changed_world DEFINITION CLOSED TYPED READY OPERATION) as [status SAME].
  subst returned; exists prefix, operation, suffix, called, called_world, changed, changed_world, status.
  split; [rewrite EVENTS, REST_EVENTS; reflexivity |]. split; [exact QUIET |].
  split; [exact PREFIX |]. split; [exact READY |]. split; assumption.
Qed.
