(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Launch paths consume exact individual SDK operations. *)
From compcert Require Import Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewaySource GatewaySpawnABI GatewayFramedRuntime GatewayLaunchPaths.

Theorem gateway_launch_sdk_operation {World Event}(backend:gateway_backend World Event)target property api
    arguments continuation memory:
  api<>gateway_posix_spawn_api->gateway_ambient_closed backend property->
  (forall before world returned after next observed,property before world->
    gateway_spawn_operation backend api arguments before world returned after next observed->
    exists middle,middle after next /\gateway_launch_path backend target middle(Returnstate returned continuation after))->
  gateway_launch_path backend target property(Callstate(gateway_spawn_signature api)arguments continuation memory).
Proof.
  intros NOT_SPAWN CLOSED EFFECT.
  assert(DIFFERENT:gateway_spawn_signature api<>gateway_spawn_signature gateway_posix_spawn_api).
  { destruct api;try contradiction;discriminate. }
  destruct api;cbn[gateway_spawn_signature]in DIFFERENT|-*.
  all:eapply gateway_launch_external;[exact DIFFERENT|exact CLOSED|].
  all:intros before world returned after next observed READY OPERATION;
    eapply EFFECT;[exact READY|];eexists;split;[apply actual_gateway_spawn_signatures|exact OPERATION].
Qed.
