(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Individual interpreter queries preserve their actual memory and heap. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers Values Memory Clight.
From HostGateway Require Import GatewayMachine GatewayRuntime GatewayPython GatewayObjects GatewayInterpreterSource
  GatewayThreadRuntime GatewayBootstrapRuntime GatewayStreamInterface.
Import ListNotations.

Record gateway_interpreter_query_post {World Event} (io : Event -> option gateway_native_io)
    native stable base (python : World -> python_world) (objects : World -> gateway_object_heap)
    (current : World -> Values.val) (identifier : World -> int64) before world after next observed : Prop := {
  gateway_interpreter_query_native : gateway_bootstrap_post io native stable base gateway_native_no_output before world after next observed;
  gateway_interpreter_query_python : python next = python world;
  gateway_interpreter_query_objects : objects next = objects world;
  gateway_interpreter_query_heap : Mem.unchanged_on (fun object _ => python_runtime_owned (python world) object) before after;
  gateway_interpreter_query_current : current next = current world;
  gateway_interpreter_query_identifier : identifier next = identifier world
}.

Record gateway_interpreter_runtime {World Event} (backend : gateway_backend World Event)
    (io : Event -> option gateway_native_io) native stable base
    (python : World -> python_world) (objects : World -> gateway_object_heap)
    (current : World -> Values.val) (identifier : World -> int64) : Prop := {
  gateway_interpreter_ambient_identity : forall before world after next,
    base None before world -> gateway_interference backend before world after next ->
    current next = current world /\ identifier next = identifier world;
  gateway_interpreter_get_operation : forall before world result after next observed,
    base None before world ->
    gateway_runtime_operation backend gateway_interpreter_get_definition [] before world result after next observed ->
    result = current world /\ (exists object offset, result = Vptr object offset) /\
    gateway_interpreter_query_post io native stable base python objects current identifier before world after next observed;
  gateway_interpreter_id_operation : forall before world result after next observed,
    base None before world ->
    gateway_runtime_operation backend gateway_interpreter_id_definition [current world]
      before world result after next observed ->
    result = Vlong (identifier world) /\
    gateway_interpreter_query_post io native stable base python objects current identifier before world after next observed
}.
