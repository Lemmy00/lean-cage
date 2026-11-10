(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Retained source tickets justify private graph frames. *)
From Stdlib Require Import List.
From HostGateway Require Import GatewayGraphSnapshots GatewayPython GatewayObjects GatewayReferences GatewayValue GatewayValueFrame
  GatewayObjectThreads GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceHeld.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_reference_held_frame {World}python objects decimal_float ledger next_ledger held world next:
  @gateway_reference_held World python objects decimal_float ledger held world->
  gateway_reference_counts_fit ledger(python world)->gateway_reference_counts_fit next_ledger(python next)->
  (forall captured,In captured held->exists place,
    gateway_reference_owns next_ledger place(gateway_held_ticket captured)(gateway_held_object captured))->
  gateway_objects_frame(python world)(objects world)(python next)(objects next)[]->
  gateway_object_privacy_frame(python world)(objects world)(python next)(objects next)[]->
  gateway_reference_held python objects decimal_float next_ledger held next.
Proof.
  intros HELD FIT NEXT_FIT RETAINED FRAME PRIVACY.
  apply Forall_forall;intros captured MEMBER.
  pose proof(proj1(Forall_forall _ _)HELD captured MEMBER)as[[old_place OWNED][PRIVATE[DESTROY VALUE]]].
  destruct(RETAINED captured MEMBER)as[place NEXT_OWNED].
  assert(OLD_ROOT:gateway_rooted(python world)(objects world)(gateway_held_object captured)).
  { eapply gateway_reference_owned_rooted;[exact FIT|exact OWNED]. }
  assert(NEXT_ROOT:gateway_rooted(python next)(objects next)(gateway_held_object captured)).
  { eapply gateway_reference_owned_rooted;[exact NEXT_FIT|exact NEXT_OWNED]. }
  destruct(gateway_private_tree_preserved _ _ _ _ _ PRIVATE DESTROY OLD_ROOT NEXT_ROOT FRAME PRIVACY)
    as[NEXT_PRIVATE NEXT_DESTROY].
  split;[exists place;exact NEXT_OWNED|]. split;[exact NEXT_PRIVATE|]. split;[exact NEXT_DESTROY|].
  destruct(gateway_held_view captured)as[wire|scalar|wire initial];cbn[gateway_held_description_holds]in VALUE|-*.
  - eapply gateway_value_heap_retained;eassumption.
  - destruct VALUE as[LOOKUP CHILDREN];split;[|exact CHILDREN].
    eapply FRAME;[exact OLD_ROOT|exact NEXT_ROOT|apply PRIVATE;constructor|intro BAD;inversion BAD|exact LOOKUP].
  - destruct VALUE as[WIRE[INITIAL SNAPSHOT]];split.
    + eapply gateway_value_heap_retained;[exact WIRE|exact PRIVATE|exact OLD_ROOT|exact NEXT_ROOT|exact FRAME|exact PRIVACY].
    + split;[exact INITIAL|]. eapply gateway_graph_snapshot_retained;
        [exact PRIVATE|exact DESTROY|exact OLD_ROOT|exact NEXT_ROOT|exact FRAME|exact PRIVACY|exact SNAPSHOT].
Qed.
