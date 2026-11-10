(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Appending an owned child cannot introduce an older mutable
   ancestor when neither the old array nor that child contains it. *)
From Stdlib Require Import List.
From HostGateway Require Import GatewayPython GatewayObjects GatewayReferences GatewayValueOwnership GatewayContainerGraph.
Import ListNotations.

Theorem gateway_array_append_separation python heap before parent pointers child next next_heap after excluded:
  gateway_object_values heap parent=Some(gateway_list_object pointers)->
  gateway_private_tree heap parent->gateway_destructible heap parent->
  gateway_private_tree heap child->gateway_destructible heap child->
  gateway_rooted python heap parent->gateway_rooted python heap child->gateway_rooted next next_heap parent->
  (forall pointer,In pointer(pointers++[child])->~gateway_object_reachable heap pointer parent)->
  ~gateway_object_reachable heap parent excluded->~gateway_object_reachable heap child excluded->
  gateway_container_return python heap before parent next next_heap after(gateway_list_object(pointers++[child]))->
  ~gateway_object_reachable next_heap parent excluded.
Proof.
  intros LOOKUP PRIVATE DESTROY CHILD_PRIVATE CHILD_DESTROY ROOT CHILD_ROOT NEXT_ROOT ACYCLIC PARENT_OUTSIDE CHILD_OUTSIDE RETURN REACHED.
  pose proof(gateway_container_value _ _ _ _ _ _ _ _ RETURN)as UPDATED.
  destruct(gateway_reachable_from_child _ _ _ _ UPDATED REACHED)as[SAME|[pointer[MEMBER PATH]]].
  - subst excluded;apply PARENT_OUTSIDE;constructor.
  - assert(NEXT_CHILD:gateway_rooted next next_heap pointer).
    { eapply gateway_child_root;[exact NEXT_ROOT|exact UPDATED|exact MEMBER]. }
    apply in_app_or in MEMBER;destruct MEMBER as[OLD|[SAME|EMPTY]].
    + assert(OLD_CHILD:gateway_object_reachable heap parent pointer).
      { eapply gateway_reachable_child;[constructor|exact LOOKUP|exact OLD]. }
      assert(CHILD_OLD_ROOT:gateway_rooted python heap pointer)by(eapply gateway_reachable_rooted;[exact ROOT|exact OLD_CHILD]).
      pose proof(gateway_private_reachable _ _ _ PRIVATE OLD_CHILD)as POINTER_PRIVATE.
      pose proof(gateway_container_region_frame _ _ _ _ _ _ _ _ _ RETURN CHILD_OLD_ROOT NEXT_CHILD POINTER_PRIVATE
        (ACYCLIC pointer ltac:(apply in_or_app;left;exact OLD)))as FRAME.
      apply PARENT_OUTSIDE;eapply gateway_reachable_trans;[exact OLD_CHILD|].
      eapply gateway_graph_frame_reachable_back;[|exact FRAME|exact PATH].
      intros object LATER;apply DESTROY;eapply gateway_reachable_trans;eassumption.
    + subst pointer.
      pose proof(gateway_container_region_frame _ _ _ _ _ _ _ _ _ RETURN CHILD_ROOT NEXT_CHILD CHILD_PRIVATE
        (ACYCLIC child ltac:(apply in_or_app;right;left;reflexivity)))as FRAME.
      apply CHILD_OUTSIDE;eapply gateway_graph_frame_reachable_back;[exact CHILD_DESTROY|exact FRAME|exact PATH].
    + contradiction.
Qed.
