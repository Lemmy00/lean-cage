(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.interfaces.gateway: IncRef credits one selected source owner even for cached aliases. *)
From Stdlib Require Import List.
From compcert Require Import Values Memory.
From HostGateway Require Import GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayObjectConstants
  GatewayObjectThreads GatewayValueOwnership GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceRuntime
  GatewayReferenceHeld GatewayReferenceRetained.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_reference_incref_held {World Event}(backend:gateway_backend World Event)
    python objects decimal_float(references:gateway_reference_runtime backend python objects)
    ledger owner held pointer value kind before world result after next observed:
  gateway_reference_ledger_well_formed ledger->gateway_reference_counts_fit ledger(python world)->
  gateway_reference_take owner(gateway_reference_entries ledger)=None->
  gateway_reference_held python objects decimal_float ledger held world->
  gateway_objects_ready(python world)(objects world)before->python_live(python world)pointer->
  gateway_object_values(objects world)pointer=Some value->gateway_object_private(objects world)pointer=true->
  gateway_object_children value=[]->gateway_object_kind value=Some kind->gateway_destructor_kind kind->
  gateway_object_operation backend gateway_api_incref[pointer]before world result after next observed->
  exists final,
    gateway_reference_apply(gateway_reference_mint owner pointer)(gateway_reference_valid ledger)=
      gateway_reference_valid final /\gateway_reference_ledger_well_formed final /\
    gateway_reference_counts_fit final(python next) /\
    gateway_reference_owns final owner(gateway_reference_next ledger)pointer /\
    gateway_reference_held python objects decimal_float final
      (held++[{|gateway_held_ticket:=gateway_reference_next ledger;gateway_held_object:=pointer;
        gateway_held_view:=gateway_held_scalar_value value|}])next /\
    gateway_objects_ready(python next)(objects next)after /\
    python_incref_return(python world)pointer before(python next)after.
Proof.
  intros FORMED FIT VACANT HELD READY LIVE VALUE PRIVATE CHILDREN KIND SAFE OPERATION.
  destruct(gateway_runtime_incref_objects _ _ _ references _ _ _ _ _ _ _ READY LIVE OPERATION)
    as[RETURN[AFTER[FRAME[PRIVACY[AFTER_VALUE AFTER_PRIVATE]]]]].
  destruct(gateway_reference_credit_mints ledger owner pointer(python world)(python next)FORMED FIT VACANT
    (gateway_incref_reference_credit _ _ _ _ _ RETURN))
    as[final[MINT[WELL[COUNTS[OWNED RETAINED]]]]].
  assert(OLD_AFTER:gateway_reference_held python objects decimal_float final held next).
  { eapply gateway_reference_held_frame;[exact HELD|exact FIT|exact COUNTS| |exact FRAME|exact PRIVACY].
    intros captured MEMBER;pose proof(proj1(Forall_forall _ _)HELD captured MEMBER)as[[place OLD]REST].
    exists place;apply RETAINED;exact OLD. }
  assert(LOOKUP:gateway_object_values(objects next)pointer=Some value)by congruence.
  assert(PROTECTED:gateway_object_private(objects next)pointer=true)by congruence.
  exists final;split;[exact MINT|]. split;[exact WELL|]. split;[exact COUNTS|]. split;[exact OWNED|]. split.
  - apply Forall_app;split;[exact OLD_AFTER|]. constructor;[|constructor].
    split;[exists owner;exact OWNED|]. split.
    + eapply gateway_leaf_private;[exact LOOKUP|exact CHILDREN|exact PROTECTED].
    + split.
      * eapply gateway_leaf_destructible;[exact LOOKUP|exact CHILDREN|exact KIND|exact SAFE].
      * split;[exact LOOKUP|exact CHILDREN].
  - split;assumption.
Qed.
