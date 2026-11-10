(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Releasing one lease retains other owned references even when cached values alias. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Values Memory.
From HostGateway Require Import GatewayGraphSnapshots GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayRootLeases
  GatewayValue GatewayValueFrame GatewayObjectThreads.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_actual_decref_keeps_held {World Event}(backend:gateway_backend World Event)
    python objects decimal_float leases
    (references:gateway_reference_runtime backend python objects)
    (roots:gateway_root_lease_runtime backend python objects decimal_float leases)
    before world consumed object result after next observed held :
  gateway_objects_ready(python world)(objects world)before ->leases world consumed object ->
  gateway_destructible(objects world)object ->gateway_held_values python objects decimal_float leases held world ->
  (forall value,In value held->gateway_held_ticket value<>consumed) ->
  gateway_object_operation backend gateway_api_decref[object]before world result after next observed ->
  gateway_reference_return(python world)(objects world)before object(python next)(objects next)after /\
    gateway_reference_released leases world next consumed /\
    gateway_held_values python objects decimal_float leases held next.
Proof.
  intros READY LEASE DESTRUCTIBLE HELD DIFFERENT OPERATION.
  pose proof(gateway_lease_rooted backend python objects decimal_float leases roots _ _ _ LEASE)as ROOT.
  assert(OWNED:(0<python_native_strong(python world)object)%nat).
  { pose proof(gateway_lease_count _ _ _ _ _ roots world object[consumed]
      ltac:(constructor;[intro BAD;inversion BAD|constructor])
      ltac:(constructor;[exact LEASE|constructor]))as COUNT;cbn in COUNT;lia. }
  pose proof(gateway_runtime_decref_objects _ _ _ references _ _ _ _ _ _ _ READY OWNED DESTRUCTIBLE OPERATION)as RETURN.
  pose proof(gateway_decref_lease _ _ _ _ _ roots _ _ _ _ _ _ _ _
    (proj1(proj1 READY))(proj1(proj2 READY))LEASE OPERATION)as RELEASED.
  split;[exact RETURN|]. split;[exact RELEASED|].
  apply Forall_forall;intros captured MEMBER.
  apply Forall_forall with(x:=captured)in HELD;[|exact MEMBER].
  destruct HELD as[OLD_LEASE[OLD_ROOT[PRIVATE[DESTROY VALUE]]]].
  assert(NEXT_LEASE:leases next(gateway_held_ticket captured)(gateway_held_object captured)).
  { apply(proj2 RELEASED);[apply DIFFERENT;exact MEMBER|exact OLD_LEASE]. }
  pose proof(gateway_lease_rooted backend python objects decimal_float leases roots _ _ _ NEXT_LEASE)as NEXT_ROOT.
  destruct(gateway_private_tree_preserved _ _ _ _ _ PRIVATE DESTROY OLD_ROOT NEXT_ROOT
    (gateway_reference_values _ _ _ _ _ _ _ RETURN)(gateway_reference_privacy _ _ _ _ _ _ _ RETURN))
    as[NEXT_PRIVATE NEXT_DESTROY].
  split;[exact NEXT_LEASE|]. split;[exact NEXT_ROOT|]. split;[exact NEXT_PRIVATE|]. split;[exact NEXT_DESTROY|].
  destruct(gateway_held_view captured)as[wire|scalar|wire initial];cbn[gateway_held_description_holds]in VALUE|-*.
  - eapply gateway_value_heap_retained;[exact VALUE|exact PRIVATE|exact OLD_ROOT|exact NEXT_ROOT|
      exact(gateway_reference_values _ _ _ _ _ _ _ RETURN)|exact(gateway_reference_privacy _ _ _ _ _ _ _ RETURN)].
  - destruct VALUE as[LOOKUP CHILDREN];split;[|exact CHILDREN].
    eapply gateway_reference_values;[exact RETURN|exact OLD_ROOT|exact NEXT_ROOT|
      apply PRIVATE;constructor|intro BAD;inversion BAD|exact LOOKUP].
  - destruct VALUE as[WIRE[INITIAL SNAPSHOT]];split.
    + eapply gateway_value_heap_retained;[exact WIRE|exact PRIVATE|exact OLD_ROOT|exact NEXT_ROOT|exact (gateway_reference_values _ _ _ _ _ _ _ RETURN)|exact (gateway_reference_privacy _ _ _ _ _ _ _ RETURN)].
    + split;[exact INITIAL|]. eapply gateway_graph_snapshot_retained;
        [exact PRIVATE|exact DESTROY|exact OLD_ROOT|exact NEXT_ROOT|exact (gateway_reference_values _ _ _ _ _ _ _ RETURN)|exact (gateway_reference_privacy _ _ _ _ _ _ _ RETURN)|exact SNAPSHOT].
Qed.
