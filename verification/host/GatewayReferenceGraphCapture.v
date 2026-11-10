(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Exact owned graph views derive later pointer edges and freshness
   exclusions from the same retained source ticket, without another physical reference. *)
From Stdlib Require Import List.
From HostGateway Require Import GatewayPython GatewayObjects GatewayReferences GatewayValue GatewayValueOwnership
  GatewayObjectThreads GatewayGraphSnapshots GatewayReferenceLedger GatewayReferenceHeld GatewayReferenceThreads
  GatewayReferenceContainerScope.
Import ListNotations.
Local Close Scope lean_scope.

Definition gateway_reference_graph_capture ticket pointer value initial:gateway_held_value:={|
  gateway_held_ticket:=ticket;gateway_held_object:=pointer;gateway_held_view:=gateway_held_graph_value value initial|}.

Theorem gateway_reference_add_graph_capture {World}python objects decimal_float ledger held world owner ticket pointer value:
  @gateway_reference_scope World python objects decimal_float ledger held world->
  gateway_reference_owns ledger owner ticket pointer->gateway_private_tree(objects world)pointer->
  gateway_destructible(objects world)pointer->gateway_value_heap decimal_float(objects world)pointer value->
  gateway_reference_scope python objects decimal_float ledger
    (held++[gateway_reference_graph_capture ticket pointer value(objects world)])world.
Proof.
  intros[FIT HELD]OWNED PRIVATE DESTROY VALUE;split;[exact FIT|]. apply Forall_app;split;[exact HELD|].
  constructor;[|constructor]. split;[exists owner;exact OWNED|]. split;[exact PRIVATE|]. split;[exact DESTROY|].
  split;[exact VALUE|]. split;[exact DESTROY|apply gateway_graph_snapshot_refl].
Qed.

Theorem gateway_reference_upgrade_wire_capture {World}python objects decimal_float ledger held world ticket pointer value:
  @gateway_reference_scope World python objects decimal_float ledger
    (held++[gateway_reference_wire_capture ticket pointer value])world->
  gateway_reference_scope python objects decimal_float ledger
    (held++[gateway_reference_graph_capture ticket pointer value(objects world)])world.
Proof.
  intro SCOPE.
  destruct(gateway_reference_capture_member _ _ _ _ _ _ _ SCOPE ltac:(apply in_or_app;right;left;reflexivity))
    as[[owner OWNED][PRIVATE[DESTROY VALUE]]].
  apply(gateway_reference_add_graph_capture python objects decimal_float ledger held world owner ticket pointer value);
    [eapply gateway_reference_scope_sublist;[exact SCOPE|intros captured MEMBER;apply in_or_app;left;exact MEMBER]|
      exact OWNED|exact PRIVATE|exact DESTROY|exact VALUE].
Qed.

Theorem gateway_reference_graph_snapshot {World}python objects decimal_float ledger held world ticket pointer value initial:
  @gateway_reference_scope World python objects decimal_float ledger held world->
  In(gateway_reference_graph_capture ticket pointer value initial)held->
  gateway_destructible initial pointer /\gateway_graph_snapshot initial(objects world)pointer.
Proof.
  intros SCOPE MEMBER.
  pose proof(gateway_reference_capture_member _ _ _ _ _ _ _ SCOPE MEMBER)as[OWNED[PRIVATE[DESTROY[VALUE SNAPSHOT]]]].
  exact SNAPSHOT.
Qed.

Theorem gateway_reference_graph_exclusion {World}python objects decimal_float ledger held world ticket pointer value initial excluded:
  @gateway_reference_scope World python objects decimal_float ledger held world->
  In(gateway_reference_graph_capture ticket pointer value initial)held->
  ~gateway_object_reachable initial pointer excluded->~gateway_object_reachable(objects world)pointer excluded.
Proof.
  intros SCOPE MEMBER OUTSIDE REACHED;apply OUTSIDE.
  destruct(gateway_reference_graph_snapshot _ _ _ _ _ _ _ _ _ _ SCOPE MEMBER)as[DESTROY SNAPSHOT].
  eapply gateway_graph_snapshot_backward;eassumption.
Qed.

Theorem gateway_reference_scalar_avoids_graph_parent {World}python objects decimal_float ledger held world ticket parent wire initial
    parent_value leaf leaf_value:
  @gateway_reference_scope World python objects decimal_float ledger held world->
  In(gateway_reference_graph_capture ticket parent wire initial)held->
  gateway_object_values initial parent=Some parent_value->gateway_mutable_container parent_value->
  gateway_object_values(objects world)leaf=Some leaf_value->gateway_object_children leaf_value=nil->
  ~gateway_mutable_container leaf_value->~gateway_object_reachable(objects world)leaf parent.
Proof.
  intros SCOPE MEMBER PARENT_VALUE MUTABLE LEAF_VALUE CHILDREN IMMUTABLE REACHED.
  pose proof(gateway_leaf_reachable _ _ _ _ LEAF_VALUE CHILDREN REACHED)as SAME;subst parent.
  destruct(gateway_reference_graph_snapshot _ _ _ _ _ _ _ _ _ _ SCOPE MEMBER)as[DESTROY SNAPSHOT].
  pose proof(SNAPSHOT leaf(gateway_reachable_root _ _))as CURRENT.
  rewrite PARENT_VALUE in CURRENT;assert(leaf_value=parent_value)by congruence;subst leaf_value;contradiction.
Qed.
