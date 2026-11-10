(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual scalar and empty-container constructors mint one retained source reference. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Values Memory.
From HostGateway Require Import GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayValueOwnership
  GatewayObjectThreads GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceRuntime GatewayReferenceHeld
  GatewayReferenceRetained.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_reference_constructed_held {World}python objects decimal_float ledger owner held
    before world pointer after next value kind:
  gateway_reference_ledger_well_formed ledger->gateway_reference_counts_fit ledger(python world)->
  gateway_reference_take owner(gateway_reference_entries ledger)=None->
  @gateway_reference_held World python objects decimal_float ledger held world->
  gateway_constructor_return(python world)(objects world)before pointer(python next)(objects next)after value->
  gateway_object_children value=[]->gateway_object_kind value=Some kind->gateway_destructor_kind kind->
  exists final,
    gateway_reference_apply(gateway_reference_mint owner pointer)(gateway_reference_valid ledger)=
      gateway_reference_valid final /\gateway_reference_ledger_well_formed final /\
    gateway_reference_counts_fit final(python next) /\
    gateway_reference_owns final owner(gateway_reference_next ledger)pointer /\
    gateway_reference_held python objects decimal_float final
      (held++[{|gateway_held_ticket:=gateway_reference_next ledger;gateway_held_object:=pointer;
        gateway_held_view:=gateway_held_scalar_value value|}])next /\
    (forall old,In old held->gateway_reference_next ledger<>gateway_held_ticket old).
Proof.
  intros FORMED FIT VACANT HELD RETURN CHILDREN KIND SAFE.
  destruct(gateway_reference_credit_mints ledger owner pointer(python world)(python next)FORMED FIT VACANT
    (gateway_constructor_reference_credit _ _ _ _ _ _ _ _ RETURN))
    as[final[APPLY[WELL[COUNTS[OWNED RETAINED]]]]].
  destruct(gateway_constructor_all_private_frames _ _ _ _ _ _ _ _ RETURN)as[FRAME PRIVACY].
  assert(OLD_AFTER:gateway_reference_held python objects decimal_float final held next).
  { eapply gateway_reference_held_frame;[exact HELD|exact FIT|exact COUNTS| |exact FRAME|exact PRIVACY].
    intros captured MEMBER;pose proof(proj1(Forall_forall _ _)HELD captured MEMBER)as[[place OLD]REST].
    exists place;apply RETAINED;exact OLD. }
  exists final;split;[exact APPLY|]. split;[exact WELL|]. split;[exact COUNTS|]. split;[exact OWNED|]. split.
  - apply Forall_app;split;[exact OLD_AFTER|]. constructor;[|constructor].
    split;[exists owner;exact OWNED|]. split.
    + eapply gateway_leaf_private;[exact(gateway_constructor_value _ _ _ _ _ _ _ _ RETURN)|exact CHILDREN|
        exact(gateway_constructor_private _ _ _ _ _ _ _ _ RETURN)].
    + split.
      * eapply gateway_leaf_destructible;[exact(gateway_constructor_value _ _ _ _ _ _ _ _ RETURN)|
          exact CHILDREN|exact KIND|exact SAFE].
      * split;[exact(gateway_constructor_value _ _ _ _ _ _ _ _ RETURN)|exact CHILDREN].
  - intros old MEMBER SAME.
    pose proof(proj1(Forall_forall _ _)HELD old MEMBER)as[[place OLD]REST].
    destruct FORMED as[_[_ BOUNDS]].
    apply Forall_forall with(x:={|gateway_reference_ticket:=gateway_held_ticket old;gateway_reference_owner:=place;
      gateway_reference_pointer:=gateway_held_object old|})in BOUNDS;[|exact OLD].
    cbn in BOUNDS;rewrite SAME in BOUNDS;exact(Nat.lt_irrefl _ BOUNDS).
Qed.

Theorem gateway_reference_actual_constructor {World Event}(backend:gateway_backend World Event)
    python objects decimal_float(constructors:gateway_objects_runtime backend python objects decimal_float)
    ledger owner held api arguments before world pointer after next observed value kind:
  gateway_reference_ledger_well_formed ledger->gateway_reference_counts_fit ledger(python world)->
  gateway_reference_take owner(gateway_reference_entries ledger)=None->
  gateway_reference_held python objects decimal_float ledger held world->
  gateway_objects_ready(python world)(objects world)before->
  gateway_constructor_request decimal_float(objects world)before api arguments value->
  gateway_constructor_roots(python world)(objects world)api arguments->
  gateway_object_operation backend api arguments before world pointer after next observed->pointer<>Values.Vnullptr->
  gateway_object_children value=[]->gateway_object_kind value=Some kind->gateway_destructor_kind kind->
  exists final,
    gateway_reference_apply(gateway_reference_mint owner pointer)(gateway_reference_valid ledger)=
      gateway_reference_valid final /\gateway_reference_ledger_well_formed final /\
    gateway_reference_counts_fit final(python next) /\
    gateway_reference_owns final owner(gateway_reference_next ledger)pointer /\
    gateway_reference_held python objects decimal_float final
      (held++[{|gateway_held_ticket:=gateway_reference_next ledger;gateway_held_object:=pointer;
        gateway_held_view:=gateway_held_scalar_value value|}])next /\
    (forall old,In old held->gateway_reference_next ledger<>gateway_held_ticket old).
Proof.
  intros FORMED FIT VACANT HELD READY REQUEST ROOTS OPERATION NONNULL CHILDREN KIND SAFE.
  eapply gateway_reference_constructed_held;try eassumption.
  eapply gateway_runtime_constructor;[exact constructors|exact READY|exact REQUEST|exact ROOTS|exact OPERATION|exact NONNULL].
Qed.
