(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: Selected operand release retains independently owned parsed graphs. *)
From Stdlib Require Import List.
From compcert Require Import Values Memory.
From HostGateway Require Import GatewayGraphSnapshots GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayValue
  GatewayValueFrame GatewayObjectThreads GatewayReferenceLedger GatewayReferenceAccounting.
Import ListNotations.
Local Close Scope lean_scope.

Definition gateway_reference_held {World}(python:World->python_world)(objects:World->gateway_object_heap)
    decimal_float ledger(held:list gateway_held_value)world:Prop:=
  Forall(fun captured=>
    (exists place,gateway_reference_owns ledger place(gateway_held_ticket captured)(gateway_held_object captured)) /\
    gateway_private_tree(objects world)(gateway_held_object captured) /\
    gateway_destructible(objects world)(gateway_held_object captured) /\
    gateway_held_description_holds decimal_float(objects world)(gateway_held_object captured)(gateway_held_view captured))held.

Theorem gateway_reference_decref_keeps_held {World Event}(backend:gateway_backend World Event)
    python objects decimal_float(references:gateway_reference_runtime backend python objects)
    ledger owner consumed pointer before world result after next_world observed held:
  gateway_reference_ledger_well_formed ledger->gateway_reference_counts_fit ledger(python world)->
  gateway_reference_owns ledger owner consumed pointer->
  gateway_objects_ready(python world)(objects world)before->gateway_destructible(objects world)pointer->
  gateway_reference_held python objects decimal_float ledger held world->
  (forall captured,In captured held->gateway_held_ticket captured<>consumed)->
  gateway_object_operation backend gateway_api_decref[pointer]before world result after next_world observed->
  exists next,
    gateway_reference_apply(gateway_reference_release owner pointer)(gateway_reference_valid ledger)=
      gateway_reference_valid next /\gateway_reference_ledger_well_formed next /\
    gateway_reference_counts_fit next(python next_world) /\
    gateway_reference_held python objects decimal_float next held next_world /\
    gateway_reference_return(python world)(objects world)before pointer(python next_world)(objects next_world)after.
Proof.
  intros FORMED FIT OWNED READY DESTRUCTIBLE HELD DIFFERENT OPERATION.
  destruct(gateway_reference_actual_decref backend python objects references ledger owner consumed pointer
    before world result after next_world observed FORMED FIT OWNED READY DESTRUCTIBLE OPERATION)
    as[next[APPLY[WELL[COUNTS[RETURN RETAINED]]]]].
  exists next;split;[exact APPLY|]. split;[exact WELL|]. split;[exact COUNTS|]. split;[|exact RETURN].
  apply Forall_forall;intros captured MEMBER.
  apply Forall_forall with(x:=captured)in HELD;[|exact MEMBER].
  destruct HELD as[[place OLD_OWNED][PRIVATE[DESTROY VALUE]]].
  assert(NEXT_OWNED:gateway_reference_owns next place(gateway_held_ticket captured)(gateway_held_object captured)).
  { apply RETAINED;[apply DIFFERENT;exact MEMBER|exact OLD_OWNED]. }
  assert(OLD_ROOT:gateway_rooted(python world)(objects world)(gateway_held_object captured)).
  { eapply gateway_reference_owned_rooted;[exact FIT|exact OLD_OWNED]. }
  assert(NEXT_ROOT:gateway_rooted(python next_world)(objects next_world)(gateway_held_object captured)).
  { eapply gateway_reference_owned_rooted;[exact COUNTS|exact NEXT_OWNED]. }
  destruct(gateway_private_tree_preserved _ _ _ _ _ PRIVATE DESTROY OLD_ROOT NEXT_ROOT
    (gateway_reference_values _ _ _ _ _ _ _ RETURN)(gateway_reference_privacy _ _ _ _ _ _ _ RETURN))
    as[NEXT_PRIVATE NEXT_DESTROY].
  split;[exists place;exact NEXT_OWNED|]. split;[exact NEXT_PRIVATE|]. split;[exact NEXT_DESTROY|].
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
