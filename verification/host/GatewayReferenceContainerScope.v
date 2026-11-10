(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Retained source tickets justify exact graph observations
   across an individual thread or readiness effect. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Values Memory.
From HostGateway Require Import GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayValue
  GatewayValueOwnership GatewayValueFrame GatewayObjectThreads GatewayContainerGraph GatewayReferenceLedger
  GatewayReferenceAccounting GatewayReferenceHeld GatewayReferenceThreads.
Import ListNotations.
Local Close Scope lean_scope.

Definition gateway_reference_wire_capture ticket object value:gateway_held_value:={|
  gateway_held_ticket:=ticket;gateway_held_object:=object;gateway_held_view:=gateway_held_wire_value value|}.

Lemma gateway_reference_capture_member {World}python objects decimal_float ledger held world captured:
  @gateway_reference_scope World python objects decimal_float ledger held world->In captured held->
  (exists owner,gateway_reference_owns ledger owner(gateway_held_ticket captured)(gateway_held_object captured)) /\
  gateway_private_tree(objects world)(gateway_held_object captured) /\
  gateway_destructible(objects world)(gateway_held_object captured) /\
  gateway_held_description_holds decimal_float(objects world)(gateway_held_object captured)(gateway_held_view captured).
Proof. intros[FIT HELD]MEMBER;apply(proj1(Forall_forall _ _)HELD captured MEMBER). Qed.

Lemma gateway_reference_thread_graph_frame {World}python objects decimal_float ledger held world next captured:
  @gateway_reference_scope World python objects decimal_float ledger held world->In captured held->
  gateway_reference_thread_effect python objects world next->
  gateway_graph_region_frame(objects world)(objects next)(gateway_held_object captured).
Proof.
  intros SCOPE MEMBER EFFECT.
  pose proof(gateway_reference_scope_thread_effect python objects decimal_float ledger held world next SCOPE EFFECT)as NEXT_SCOPE.
  destruct(gateway_reference_capture_member _ _ _ _ _ _ _ SCOPE MEMBER)as[[owner OWNED][PRIVATE[DESTROY VALUE]]].
  assert(ROOT:gateway_rooted(python world)(objects world)(gateway_held_object captured)).
  { eapply gateway_reference_owned_rooted;[exact(proj1 SCOPE)|exact OWNED]. }
  assert(NEXT_ROOT:gateway_rooted(python next)(objects next)(gateway_held_object captured)).
  { eapply gateway_reference_owned_rooted;[exact(proj1 NEXT_SCOPE)|exact OWNED]. }
  intros object REACHED.
  destruct(gateway_private_tree_frame _ _ _ _ _ PRIVATE ROOT NEXT_ROOT
    (gateway_reference_thread_values _ _ _ _ EFFECT)(gateway_reference_thread_privacy _ _ _ _ EFFECT)object REACHED)
    as[OLD[NEW[VALUES PRIVACY]]];split;assumption.
Qed.

Theorem gateway_reference_thread_keeps_graph_exclusion {World}python objects decimal_float ledger held world next captured excluded:
  @gateway_reference_scope World python objects decimal_float ledger held world->In captured held->
  ~gateway_object_reachable(objects world)(gateway_held_object captured)excluded->
  gateway_reference_thread_effect python objects world next->
  ~gateway_object_reachable(objects next)(gateway_held_object captured)excluded.
Proof.
  intros SCOPE MEMBER OUTSIDE EFFECT REACHED;apply OUTSIDE.
  eapply gateway_graph_frame_reachable_back;[|eapply gateway_reference_thread_graph_frame;eassumption|exact REACHED].
  exact(proj1(proj2(proj2(gateway_reference_capture_member _ _ _ _ _ _ _ SCOPE MEMBER)))).
Qed.

Lemma gateway_reference_scope_sublist {World}python objects decimal_float ledger held selected world:
  @gateway_reference_scope World python objects decimal_float ledger held world->
  (forall captured,In captured selected->In captured held)->
  gateway_reference_scope python objects decimal_float ledger selected world.
Proof.
  intros[FIT HELD]SUBSET;split;[exact FIT|]. apply Forall_forall;intros captured MEMBER.
  exact(proj1(Forall_forall _ _)HELD captured(SUBSET captured MEMBER)).
Qed.

Lemma gateway_reference_add_wire_capture {World}python objects decimal_float ledger held world owner ticket pointer value:
  @gateway_reference_scope World python objects decimal_float ledger held world->
  gateway_reference_owns ledger owner ticket pointer->gateway_private_tree(objects world)pointer->
  gateway_destructible(objects world)pointer->gateway_value_heap decimal_float(objects world)pointer value->
  gateway_reference_scope python objects decimal_float ledger(held++[gateway_reference_wire_capture ticket pointer value])world.
Proof.
  intros[FIT HELD]OWNED PRIVATE DESTROY VALUE;split;[exact FIT|]. apply Forall_app;split;[exact HELD|].
  constructor;[|constructor]. split;[exists owner;exact OWNED|]. split;[exact PRIVATE|]. split;assumption.
Qed.
