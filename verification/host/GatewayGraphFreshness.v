(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Fresh mutable constructors cannot alias an earlier owned private graph. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Values Memory.
From HostGateway Require Import GatewayPython GatewayObjects GatewayReferences GatewayRootLeases GatewayObjectThreads GatewayValueOwnership.
Import ListNotations.

Definition gateway_held_graphs_avoid heap held object :Prop:=
  forall old,In old held ->~gateway_object_reachable heap(gateway_held_object old)object.

Lemma gateway_held_graphs_avoid_retained {World}python objects decimal_float leases held world next object :
  @gateway_held_values World python objects decimal_float leases held world ->
  gateway_held_values python objects decimal_float leases held next ->
  gateway_objects_frame(python world)(objects world)(python next)(objects next)[] ->
  gateway_object_privacy_frame(python world)(objects world)(python next)(objects next)[] ->
  gateway_held_graphs_avoid(objects world)held object ->gateway_held_graphs_avoid(objects next)held object.
Proof.
  intros BEFORE AFTER FRAME PRIVACY AVOIDS old MEMBER REACHED.
  pose proof(proj1(Forall_forall _ _)BEFORE old MEMBER)as[OLD_LEASE[OLD_ROOT[PRIVATE[DESTRUCTIBLE DESCRIPTION]]]].
  pose proof(proj1(Forall_forall _ _)AFTER old MEMBER)as[NEW_LEASE[NEW_ROOT REST]].
  apply(AVOIDS old MEMBER).
  eapply gateway_private_tree_reachable_back;[exact PRIVATE|exact DESTRUCTIBLE|exact OLD_ROOT|exact NEW_ROOT|exact FRAME|exact PRIVACY|exact REACHED].
Qed.

Theorem gateway_constructor_avoids_held_graphs {World}python objects decimal_float leases held
    before world result after next value:
  gateway_constructor_return(python world)(objects world)before result(python next)(objects next)after value ->
  gateway_objects_ready(python world)(objects world)before ->gateway_mutable_container value ->
  @gateway_held_values World python objects decimal_float leases held world ->
  gateway_held_values python objects decimal_float leases held next ->
  gateway_held_graphs_avoid(objects next)held result.
Proof.
  intros RETURN READY MUTABLE BEFORE AFTER.
  destruct(gateway_constructor_all_private_frames _ _ _ _ _ _ _ _ RETURN)as[FRAME PRIVACY].
  eapply gateway_held_graphs_avoid_retained;[exact BEFORE|exact AFTER|exact FRAME|exact PRIVACY|].
  intros old MEMBER.
  pose proof(proj1(Forall_forall _ _)BEFORE old MEMBER)as[LEASE[ROOT REST]].
  eapply gateway_new_container_outside_old_graph;[exact RETURN|exact READY|exact MUTABLE|exact ROOT].
Qed.
