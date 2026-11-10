(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Recursive value receipts retain older exact graphs and exclude
   their mutable roots from newly decoded immutable leaves. *)
From Stdlib Require Import List.
From HostGateway Require Import GatewayPython GatewayObjects GatewayReferences GatewayValue GatewayObjectThreads
  GatewayReferenceLedger GatewayReferenceHeld GatewayReferenceThreads GatewayReferenceContainerScope
  GatewayReferenceGraphCapture.
Import ListNotations.
Local Close Scope lean_scope.

Definition gateway_reference_graphs_only held:Prop:=
  forall captured,In captured held->exists wire initial,gateway_held_view captured=gateway_held_graph_value wire initial.

Definition gateway_reference_avoids_old_mutable held heap pointer:Prop:=
  forall captured,In captured held->forall wire initial,
    gateway_held_view captured=gateway_held_graph_value wire initial->forall value,
      gateway_object_values initial(gateway_held_object captured)=Some value->gateway_mutable_container value->
      ~gateway_object_reachable heap pointer(gateway_held_object captured).

Theorem gateway_reference_graph_result {World}python objects decimal_float ledger held captured world wire:
  @gateway_reference_scope World python objects decimal_float ledger(held++[captured])world->
  gateway_value_heap decimal_float(objects world)(gateway_held_object captured)wire->
  gateway_reference_scope python objects decimal_float ledger
    (held++[gateway_reference_graph_capture(gateway_held_ticket captured)(gateway_held_object captured)wire(objects world)])world.
Proof.
  intros SCOPE VALUE.
  destruct(gateway_reference_capture_member _ _ _ _ _ _ _ SCOPE ltac:(apply in_or_app;right;left;reflexivity))
    as[[owner OWNED][PRIVATE[DESTROY DESCRIPTION]]].
  eapply gateway_reference_add_graph_capture;
    [eapply gateway_reference_scope_sublist;[exact SCOPE|intros previous MEMBER;apply in_or_app;left;exact MEMBER]|
      exact OWNED|exact PRIVATE|exact DESTROY|exact VALUE].
Qed.

Theorem gateway_reference_leaf_excludes_old_mutable {World}python objects decimal_float ledger held world pointer leaf:
  @gateway_reference_scope World python objects decimal_float ledger held world->
  gateway_object_values(objects world)pointer=Some leaf->gateway_object_children leaf=nil->
  ~gateway_mutable_container leaf->gateway_reference_avoids_old_mutable held(objects world)pointer.
Proof.
  intros SCOPE LOOKUP CHILDREN IMMUTABLE captured MEMBER wire initial VIEW value OLD MUTABLE.
  destruct captured as[ticket parent description];cbn in VIEW|-*;subst description.
  eapply gateway_reference_scalar_avoids_graph_parent;
    [exact SCOPE|exact MEMBER|exact OLD|exact MUTABLE|exact LOOKUP|exact CHILDREN|exact IMMUTABLE].
Qed.

Lemma gateway_reference_graphs_only_append held captured:
  gateway_reference_graphs_only held->
  (exists wire initial,gateway_held_view captured=gateway_held_graph_value wire initial)->
  gateway_reference_graphs_only(held++[captured]).
Proof.
  intros OLD NEW previous MEMBER;apply in_app_or in MEMBER;destruct MEMBER as[OLD_MEMBER|[SAME|EMPTY]];
    [apply OLD;exact OLD_MEMBER|subst previous;exact NEW|contradiction].
Qed.
