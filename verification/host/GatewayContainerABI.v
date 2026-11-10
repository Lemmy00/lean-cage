(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Actual builtin container calls have their individual integer ABI. *)
From Stdlib Require Import List ZArith.
From compcert Require Import Integers Values Memory.
From HostGateway Require Import GatewayMachine GatewayPython GatewayObjects.
Import ListNotations.

Record gateway_container_abi_runtime {World Event}(backend:gateway_backend World Event)
    (python:World->python_world)(objects:World->gateway_object_heap):Prop:={
  gateway_list_append_integer:forall before world container values child result after next observed,
    gateway_objects_ready(python world)(objects world)before ->
    gateway_rooted(python world)(objects world)container ->gateway_rooted(python world)(objects world)child ->
    gateway_object_values(objects world)container=Some(gateway_list_object values) ->
    gateway_object_operation backend gateway_api_list_append[container;child]before world result after next observed ->
    exists status,result=Vint status;
  gateway_dict_contains_integer:forall before world dictionary fields key characters result after next observed,
    gateway_objects_ready(python world)(objects world)before ->
    gateway_rooted(python world)(objects world)dictionary ->gateway_rooted(python world)(objects world)key ->
    gateway_object_values(objects world)dictionary=Some(gateway_dict_object fields) ->
    gateway_object_values(objects world)key=Some(gateway_unicode_object characters) ->
    gateway_object_operation backend gateway_api_dict_contains[dictionary;key]before world result after next observed ->
    exists status,result=Vint status;
  gateway_dict_insert_integer:forall before world dictionary fields key characters child result after next observed,
    gateway_objects_ready(python world)(objects world)before ->
    gateway_rooted(python world)(objects world)dictionary ->gateway_rooted(python world)(objects world)key ->
    gateway_rooted(python world)(objects world)child ->
    gateway_object_values(objects world)dictionary=Some(gateway_dict_object fields) ->
    gateway_object_values(objects world)key=Some(gateway_unicode_object characters) ->
    gateway_object_operation backend gateway_api_dict_set[dictionary;key;child]before world result after next observed ->
    exists status,result=Vint status
}.
