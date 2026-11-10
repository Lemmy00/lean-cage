(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Source-owned graph snapshots retain exact reachable
   pointer edges without freezing unrelated or public heap objects. *)
From Stdlib Require Import List.
From HostGateway Require Import GatewayPython GatewayObjects GatewayReferences.

Definition gateway_graph_snapshot initial current root:Prop:=
  forall object,gateway_object_reachable initial root object->
    gateway_object_values current object=gateway_object_values initial object.

Lemma gateway_graph_snapshot_refl heap root:gateway_graph_snapshot heap heap root.
Proof. intros object REACHED;reflexivity. Qed.

Lemma gateway_graph_snapshot_forward initial current root:
  gateway_graph_snapshot initial current root->forall object,
    gateway_object_reachable initial root object->gateway_object_reachable current root object.
Proof.
  intros SNAPSHOT object REACHED;induction REACHED;[constructor|].
  eapply gateway_reachable_child;[exact IHREACHED|rewrite SNAPSHOT by exact REACHED;exact H|exact H0].
Qed.

Lemma gateway_graph_snapshot_backward initial current root:
  gateway_destructible initial root->gateway_graph_snapshot initial current root->forall object,
    gateway_object_reachable current root object->gateway_object_reachable initial root object.
Proof.
  intros DESTROY SNAPSHOT object REACHED;induction REACHED;[constructor|].
  destruct(DESTROY parent IHREACHED)as[old[kind[LOOKUP REST]]].
  assert(SAME:old=value)by(rewrite SNAPSHOT in H by exact IHREACHED;congruence).
  subst old;eapply gateway_reachable_child;eassumption.
Qed.

Theorem gateway_graph_snapshot_retained python heap next next_heap initial root:
  gateway_private_tree heap root->gateway_destructible heap root->
  gateway_rooted python heap root->gateway_rooted next next_heap root->
  gateway_objects_frame python heap next next_heap nil->gateway_object_privacy_frame python heap next next_heap nil->
  gateway_graph_snapshot initial heap root->gateway_graph_snapshot initial next_heap root.
Proof.
  intros PRIVATE DESTROY ROOT NEXT FRAME PRIVACY SNAPSHOT object REACHED.
  pose proof(gateway_graph_snapshot_forward _ _ _ SNAPSHOT object REACHED)as CURRENT.
  destruct(DESTROY object CURRENT)as[value[kind[LOOKUP REST]]].
  destruct(gateway_private_tree_frame _ _ _ _ _ PRIVATE ROOT NEXT FRAME PRIVACY object CURRENT)as[_[_[VALUES OWNED]]].
  rewrite<-(SNAPSHOT object REACHED),LOOKUP;apply VALUES;exact LOOKUP.
Qed.
