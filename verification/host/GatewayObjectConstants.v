(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: The SDK singleton address denotes the runtime's immutable None payload. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Values Memory.
From HostGateway Require Import GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayRootLeases
  GatewayValue GatewayObjectThreads GatewayValueOwnership.
Import ListNotations.
Local Close Scope lean_scope.

(* This is the standard interpreter singleton identity input. The source caller
   separately proves its actual SDK symbol address and performs its own IncRef.
   Protected payloads include shared immutable scalars; mutable trees need ownership. *)
Record gateway_none_runtime {World}(python:World->python_world)(objects:World->gateway_object_heap)
    (none:Values.val) :Prop:={
  gateway_none_identity:forall before world,gateway_objects_ready(python world)(objects world)before ->
    python_live(python world)none /\gateway_object_values(objects world)none=Some gateway_none_object /\
    gateway_object_private(objects world)none=true
}.

Theorem gateway_actual_none_reference_held {World Event}(backend:gateway_backend World Event)
    python objects decimal_float leases none
    (references:gateway_reference_runtime backend python objects)
    (roots:gateway_root_lease_runtime backend python objects decimal_float leases)
    (constants:gateway_none_runtime python objects none)
    before world result after next observed :
  gateway_objects_ready(python world)(objects world)before ->
  gateway_object_operation backend gateway_api_incref[none]before world result after next observed ->
  exists ticket,gateway_reference_created leases world next none ticket /\
    gateway_objects_ready(python next)(objects next)after /\
    gateway_held_values python objects decimal_float leases
      [{|gateway_held_ticket:=ticket;gateway_held_object:=none;
        gateway_held_view:=gateway_held_scalar_value gateway_none_object|}]next /\
    python_incref_return(python world)none before(python next)after.
Proof.
  intros READY OPERATION.
  destruct(gateway_none_identity _ _ _ constants _ _ READY)as[LIVE[VALUE PRIVATE]].
  destruct(gateway_runtime_incref_objects _ _ _ references _ _ _ _ _ _ _ READY LIVE OPERATION)
    as[RETURN[AFTER_READY[FRAME[PRIVACY[AFTER_VALUE AFTER_PRIVATE]]]]].
  destruct(gateway_incref_lease _ _ _ _ _ roots _ _ _ _ _ _ _
    (proj1(proj1 READY))(proj1(proj2 READY))LIVE OPERATION)as[ticket CREATED].
  assert(LOOKUP:gateway_object_values(objects next)none=Some gateway_none_object)by congruence.
  assert(PRIVATE_NEXT:gateway_object_private(objects next)none=true)by congruence.
  exists ticket;split;[exact CREATED|]. split;[exact AFTER_READY|]. split;[|exact RETURN].
  constructor;[|constructor].
  split;[exact(proj1 CREATED)|].
  split;[eapply gateway_lease_rooted;[exact roots|exact(proj1 CREATED)]|].
  split;[eapply gateway_leaf_private;[exact LOOKUP|reflexivity|exact PRIVATE_NEXT]|].
  split.
  - eapply gateway_leaf_destructible;[exact LOOKUP|reflexivity|reflexivity|left;reflexivity].
  - split;[exact LOOKUP|reflexivity].
Qed.

Theorem gateway_incref_native_frame python heap before object next after :
  gateway_objects_ready python heap before ->python_incref_return python object before next after ->
  python_private_frame python before after.
Proof.
  intros[[WORLD_VALID REST]READY]RETURN.
  destruct(python_incref_live _ _ _ _ _ RETURN)as[STRONG[value LOOKUP]].
  destruct(python_incref_object _ _ _ _ _ RETURN)as[object_block[offset[OBJECT FRAME]]].
  destruct WORLD_VALID as[COUNTS[BYTES[BLOCKS VALUES]]].
  destruct(VALUES object value LOOKUP STRONG)as[[actual_block[actual_offset[ACTUAL OWNED]]]OTHER].
  rewrite OBJECT in ACTUAL;inversion ACTUAL;subst actual_block actual_offset.
  eapply Mem.unchanged_on_implies;[exact FRAME|].
  intros candidate position NATIVE LIVE SAME;subst candidate;exact(NATIVE OWNED).
Qed.
