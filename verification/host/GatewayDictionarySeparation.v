(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: An owned dictionary insertion cannot introduce an excluded
   mutable ancestor through its original entries or the selected key/value graphs. *)
From Stdlib Require Import List.
From HostGateway Require Import GatewayPython GatewayObjects GatewayReferences GatewayValueOwnership GatewayContainerGraph.
Import ListNotations.

Theorem gateway_dictionary_insert_separation python heap before parent fields key characters child next next_heap after excluded:
  gateway_object_values heap parent=Some(gateway_dict_object fields)->
  gateway_private_tree heap parent->gateway_destructible heap parent->
  gateway_private_tree heap key->gateway_destructible heap key->
  gateway_private_tree heap child->gateway_destructible heap child->
  gateway_rooted python heap parent->gateway_rooted python heap key->gateway_rooted python heap child->
  gateway_rooted next next_heap parent->
  (forall pointer,In pointer(gateway_dictionary_children fields++[key;child])->~gateway_object_reachable heap pointer parent)->
  ~gateway_object_reachable heap parent excluded->~gateway_object_reachable heap key excluded->
  ~gateway_object_reachable heap child excluded->
  gateway_container_return python heap before parent next next_heap after
    (gateway_dict_object(fields++[{|gateway_dictionary_key:=key;gateway_dictionary_text:=characters;gateway_dictionary_value:=child|}]))->
  ~gateway_object_reachable next_heap parent excluded.
Proof.
  intros LOOKUP PRIVATE DESTROY KEY_PRIVATE KEY_DESTROY CHILD_PRIVATE CHILD_DESTROY ROOT KEY_ROOT CHILD_ROOT NEXT_ROOT
    ACYCLIC PARENT_OUTSIDE KEY_OUTSIDE CHILD_OUTSIDE RETURN REACHED.
  pose proof(gateway_container_value _ _ _ _ _ _ _ _ RETURN)as UPDATED.
  destruct(gateway_reachable_from_child _ _ _ _ UPDATED REACHED)as[SAME|[pointer[MEMBER PATH]]].
  - subst excluded;apply PARENT_OUTSIDE;constructor.
  - change(In pointer(gateway_dictionary_children(fields++[{|gateway_dictionary_key:=key;
      gateway_dictionary_text:=characters;gateway_dictionary_value:=child|}])))in MEMBER.
    assert(NEXT_CHILD:gateway_rooted next next_heap pointer).
    { eapply gateway_child_root;[exact NEXT_ROOT|exact UPDATED|exact MEMBER]. }
    unfold gateway_dictionary_children in MEMBER;rewrite flat_map_app in MEMBER;cbn in MEMBER.
    apply in_app_or in MEMBER;destruct MEMBER as[OLD|[SAME|[SAME|EMPTY]]].
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
      pose proof(gateway_container_region_frame _ _ _ _ _ _ _ _ _ RETURN KEY_ROOT NEXT_CHILD KEY_PRIVATE
        (ACYCLIC key ltac:(apply in_or_app;right;left;reflexivity)))as FRAME.
      apply KEY_OUTSIDE;eapply gateway_graph_frame_reachable_back;[exact KEY_DESTROY|exact FRAME|exact PATH].
    + subst pointer.
      pose proof(gateway_container_region_frame _ _ _ _ _ _ _ _ _ RETURN CHILD_ROOT NEXT_CHILD CHILD_PRIVATE
        (ACYCLIC child ltac:(apply in_or_app;right;right;left;reflexivity)))as FRAME.
      apply CHILD_OUTSIDE;eapply gateway_graph_frame_reachable_back;[exact CHILD_DESTROY|exact FRAME|exact PATH].
    + contradiction.
Qed.
