(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Container mutation frames only the exact private graph
   regions disjoint from its selected receiver. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Integers Values Memory.
From HostGateway Require Import GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayValue
  GatewayValueFrame GatewayValueOwnership GatewayObjectThreads GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceHeld
  GatewayReferenceThreads GatewayGraphSnapshots.
Import ListNotations.
Local Close Scope lean_scope.

Definition gateway_graph_region_frame heap next_heap root :Prop:=
  forall object,gateway_object_reachable heap root object->
    (forall value,gateway_object_values heap object=Some value->gateway_object_values next_heap object=Some value) /\
    gateway_object_private next_heap object=true.

Lemma gateway_graph_frame_reachable_back heap next_heap root:
  gateway_destructible heap root->gateway_graph_region_frame heap next_heap root->
  forall object,gateway_object_reachable next_heap root object->gateway_object_reachable heap root object.
Proof.
  intros DESTROY FRAME object REACHED;induction REACHED;[constructor|].
  destruct(DESTROY parent IHREACHED)as[old[kind[LOOKUP REST]]].
  pose proof(proj1(FRAME parent IHREACHED)old LOOKUP)as SAME.
  assert(old=value)by congruence;subst old;eapply gateway_reachable_child;eassumption.
Qed.

Lemma gateway_graph_frame_tree heap next_heap root:
  gateway_destructible heap root->gateway_graph_region_frame heap next_heap root->
  gateway_private_tree next_heap root /\gateway_destructible next_heap root.
Proof.
  intros DESTROY FRAME;split;intros object REACHED;
    pose proof(gateway_graph_frame_reachable_back _ _ _ DESTROY FRAME object REACHED)as OLD.
  - exact(proj2(FRAME object OLD)).
  - destruct(DESTROY object OLD)as[value[kind[LOOKUP[KIND SAFE]]]].
    exists value,kind;split;[apply(proj1(FRAME object OLD));exact LOOKUP|]. split;assumption.
Qed.

Lemma gateway_graph_frame_value decimal_float heap next_heap root value:
  gateway_graph_region_frame heap next_heap root->gateway_value_heap decimal_float heap root value->
  gateway_value_heap decimal_float next_heap root value.
Proof.
  intros FRAME VALUE;destruct(gateway_value_tree_map decimal_float heap next_heap)as[MAP _].
  eapply MAP;[exact VALUE|constructor|]. intros object actual REACHED LOOKUP.
  apply(proj1(FRAME object REACHED));exact LOOKUP.
Qed.

Theorem gateway_container_region_frame python heap before container next next_heap after value root:
  gateway_container_return python heap before container next next_heap after value->
  gateway_rooted python heap root->gateway_rooted next next_heap root->gateway_private_tree heap root->
  ~gateway_object_reachable heap root container->gateway_graph_region_frame heap next_heap root.
Proof.
  intros RETURN ROOT NEXT PRIVATE OUTSIDE object REACHED.
  assert(REGION:forall object,gateway_object_reachable heap root object->
    gateway_rooted next next_heap object /\
    (forall old,gateway_object_values heap object=Some old->gateway_object_values next_heap object=Some old) /\
    gateway_object_private next_heap object=true).
  { intros candidate REACH;induction REACH.
    - assert(DIFFERENT:root<>container)by(intro SAME;subst root;apply OUTSIDE;constructor).
      split;[exact NEXT|]. split.
      + intros old LOOKUP;eapply gateway_container_values;[exact RETURN|exact ROOT|exact NEXT|apply PRIVATE;constructor|
          intros[SAME|NONE];[congruence|contradiction]|exact LOOKUP].
      + eapply gateway_container_privacy;[exact RETURN|exact ROOT|exact NEXT|apply PRIVATE;constructor|
          intros[SAME|NONE];[congruence|contradiction]].
    - destruct IHREACH as[PARENT[PARENT_VALUE PARENT_PRIVATE]].
      assert(OLD_CHILD:gateway_rooted python heap child).
      { eapply gateway_child_root;[|exact H|exact H0].
        eapply GatewayValueOwnership.gateway_reachable_rooted;[exact ROOT|exact REACH]. }
      assert(NEXT_CHILD:gateway_rooted next next_heap child).
      { eapply gateway_child_root;[exact PARENT|apply PARENT_VALUE;exact H|exact H0]. }
      assert(CHILD_REACH:gateway_object_reachable heap root child)by(eapply gateway_reachable_child;eassumption).
      assert(DIFFERENT:child<>container)by(intro SAME;subst child;apply OUTSIDE;exact CHILD_REACH).
      split;[exact NEXT_CHILD|]. split.
      + intros old LOOKUP;eapply gateway_container_values;[exact RETURN|exact OLD_CHILD|exact NEXT_CHILD|apply PRIVATE;exact CHILD_REACH|
          intros[SAME|NONE];[congruence|contradiction]|exact LOOKUP].
      + eapply gateway_container_privacy;[exact RETURN|exact OLD_CHILD|exact NEXT_CHILD|apply PRIVATE;exact CHILD_REACH|
          intros[SAME|NONE];[congruence|contradiction]]. }
  exact(proj2(REGION object REACHED)).
Qed.

Theorem gateway_container_keeps_outside_held {World}python objects decimal_float ledger held world next
    before container after value:
  @gateway_reference_scope World python objects decimal_float ledger held world->
  gateway_container_return(python world)(objects world)before container(python next)(objects next)after value->
  (forall captured,In captured held->~gateway_object_reachable(objects world)(gateway_held_object captured)container)->
  gateway_reference_scope python objects decimal_float ledger held next.
Proof.
  intros[FIT HELD]RETURN OUTSIDE.
  assert(NEXT_FIT:gateway_reference_counts_fit ledger(python next)).
  { intro pointer;rewrite(gateway_container_references _ _ _ _ _ _ _ _ RETURN pointer)by(intro NONE;inversion NONE);apply FIT. }
  split;[exact NEXT_FIT|]. apply Forall_forall;intros captured MEMBER.
  pose proof(proj1(Forall_forall _ _)HELD captured MEMBER)as[[owner OWNED][PRIVATE[DESTROY DESCRIPTION]]].
  assert(ROOT:gateway_rooted(python world)(objects world)(gateway_held_object captured)).
  { eapply gateway_reference_owned_rooted;eassumption. }
  assert(NEXT_ROOT:gateway_rooted(python next)(objects next)(gateway_held_object captured)).
  { eapply gateway_reference_owned_rooted;eassumption. }
  pose proof(gateway_container_region_frame _ _ _ _ _ _ _ _ _ RETURN ROOT NEXT_ROOT PRIVATE(OUTSIDE captured MEMBER))as FRAME.
  destruct(gateway_graph_frame_tree _ _ _ DESTROY FRAME)as[NEW_PRIVATE NEW_DESTROY].
  split;[exists owner;exact OWNED|]. split;[exact NEW_PRIVATE|]. split;[exact NEW_DESTROY|].
  destruct(gateway_held_view captured)as[wire|scalar|wire initial];cbn[gateway_held_description_holds]in DESCRIPTION|-*.
  - eapply gateway_graph_frame_value;eassumption.
  - destruct DESCRIPTION as[LOOKUP CHILDREN];split;[apply(proj1(FRAME _ (gateway_reachable_root _ _)));exact LOOKUP|exact CHILDREN].
  - destruct DESCRIPTION as[WIRE[INITIAL SNAPSHOT]];split.
    + eapply gateway_graph_frame_value;eassumption.
    + split;[exact INITIAL|]. intros pointer REACHED.
      pose proof(gateway_graph_snapshot_forward _ _ _ SNAPSHOT pointer REACHED)as CURRENT.
      destruct(DESTROY pointer CURRENT)as[actual[kind[LOOKUP REST]]].
      rewrite<-(SNAPSHOT pointer REACHED),LOOKUP;apply(proj1(FRAME pointer CURRENT));exact LOOKUP.
Qed.

Lemma gateway_reachable_from_child heap root value object:
  gateway_object_values heap root=Some value->gateway_object_reachable heap root object->
  object=root \/exists child,In child(gateway_object_children value) /\gateway_object_reachable heap child object.
Proof.
  intros LOOKUP REACHED;induction REACHED;[left;reflexivity|].
  destruct IHREACHED as[SAME|[first[MEMBER PATH]]].
  - subst parent;assert(value0=value)by congruence;subst value0;right;exists child;split;[exact H0|constructor].
  - right;exists first;split;[exact MEMBER|eapply gateway_reachable_child;eassumption].
Qed.

Lemma gateway_graph_from_children heap root value kind:
  gateway_object_values heap root=Some value->gateway_object_private heap root=true->
  gateway_object_kind value=Some kind->gateway_destructor_kind kind->
  (forall child,In child(gateway_object_children value)->gateway_private_tree heap child /\gateway_destructible heap child)->
  gateway_private_tree heap root /\gateway_destructible heap root.
Proof.
  intros LOOKUP PRIVATE KIND SAFE CHILDREN;split;intros object REACHED;
    destruct(gateway_reachable_from_child _ _ _ _ LOOKUP REACHED)as[SAME|[child[MEMBER PATH]]].
  - subst object;exact PRIVATE.
  - apply(proj1(CHILDREN child MEMBER));exact PATH.
  - subst object;exists value,kind;auto.
  - apply(proj2(CHILDREN child MEMBER));exact PATH.
Qed.

Lemma gateway_array_heap_append decimal_float heap first first_values second second_values:
  gateway_array_heap decimal_float heap first first_values->gateway_array_heap decimal_float heap second second_values->
  gateway_array_heap decimal_float heap(first++second)(first_values++second_values).
Proof. intros FIRST SECOND;induction FIRST;cbn;[exact SECOND|constructor;assumption]. Qed.

Lemma gateway_graph_frame_reachable_forward heap next_heap root:
  gateway_graph_region_frame heap next_heap root->
  forall object,gateway_object_reachable heap root object->gateway_object_reachable next_heap root object.
Proof.
  intros FRAME object REACHED;induction REACHED;[constructor|].
  eapply gateway_reachable_child;[exact IHREACHED|apply(proj1(FRAME parent REACHED));exact H|exact H0].
Qed.

Lemma gateway_graph_region_frame_trans first middle last root:
  gateway_graph_region_frame first middle root->gateway_graph_region_frame middle last root->
  gateway_graph_region_frame first last root.
Proof.
  intros FIRST SECOND object REACHED.
  pose proof(gateway_graph_frame_reachable_forward _ _ _ FIRST object REACHED)as NEXT_REACHED.
  split;[|exact(proj2(SECOND object NEXT_REACHED))].
  intros value LOOKUP;apply(proj1(SECOND object NEXT_REACHED));apply(proj1(FIRST object REACHED));exact LOOKUP.
Qed.

Lemma gateway_graph_region_frame_child heap next_heap root child:
  gateway_graph_region_frame heap next_heap root->gateway_object_reachable heap root child->
  gateway_graph_region_frame heap next_heap child.
Proof. intros FRAME REACHED object LATER;apply FRAME;eapply gateway_reachable_trans;eassumption. Qed.
