(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Borrowed container arguments retain the invocation's C-owned leases. *)
From Stdlib Require Import List ZArith.
From compcert Require Import Integers Values Memory.
From HostGateway Require Import GatewayMachine GatewayPython GatewayObjects GatewayRootLeases.
Import ListNotations.

Record gateway_container_lease_runtime {World Event}(backend:gateway_backend World Event)
    (python:World->python_world)(objects:World->gateway_object_heap)(leases:World->nat->Values.val->Prop):Prop:={
  gateway_list_append_leases:forall before world container values child status after next observed,
    gateway_objects_ready(python world)(objects world)before ->
    gateway_rooted(python world)(objects world)container ->gateway_rooted(python world)(objects world)child ->
    gateway_object_private(objects world)container=true ->
    gateway_object_values(objects world)container=Some(gateway_list_object values) ->
    gateway_object_operation backend gateway_api_list_append[container;child]before world(Vint status)after next observed ->
    gateway_leases_retained leases world next;
  gateway_dict_contains_leases:forall before world dictionary fields key characters status after next observed,
    gateway_objects_ready(python world)(objects world)before ->
    gateway_rooted(python world)(objects world)dictionary ->gateway_rooted(python world)(objects world)key ->
    gateway_object_values(objects world)dictionary=Some(gateway_dict_object fields) ->
    gateway_object_values(objects world)key=Some(gateway_unicode_object characters) ->
    gateway_object_operation backend gateway_api_dict_contains[dictionary;key]before world(Vint status)after next observed ->
    gateway_leases_retained leases world next;
  gateway_dict_insert_leases:forall before world dictionary fields key characters child status after next observed,
    gateway_objects_ready(python world)(objects world)before ->
    gateway_rooted(python world)(objects world)dictionary ->gateway_rooted(python world)(objects world)key ->
    gateway_rooted(python world)(objects world)child ->gateway_object_private(objects world)dictionary=true ->
    gateway_object_values(objects world)dictionary=Some(gateway_dict_object fields) ->
    gateway_object_values(objects world)key=Some(gateway_unicode_object characters) ->
    gateway_dictionary_lookup characters fields=None ->
    gateway_object_operation backend gateway_api_dict_set[dictionary;key;child]before world(Vint status)after next observed ->
    gateway_leases_retained leases world next
}.
