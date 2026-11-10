(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A real IncRef owns a selected borrowed graph before releasing its container. *)
From Stdlib Require Import List.
From compcert Require Import Values Memory.
From HostGateway Require Import GatewayGraphSnapshots GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayValue
  GatewayValueFrame GatewayObjectThreads GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceRuntime
  GatewayReferenceHeld GatewayReferenceRetained GatewayPublicReferences GatewayAttachedReferences.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_reference_incref_borrowed_graph {World Event}(backend:gateway_backend World Event)
    python objects decimal_float(references:gateway_reference_runtime backend python objects)
    ledger owner held pointer description before world result after next observed:
  gateway_reference_ledger_well_formed ledger->gateway_reference_counts_fit ledger(python world)->
  gateway_reference_take owner(gateway_reference_entries ledger)=None->
  gateway_reference_held python objects decimal_float ledger held world->
  gateway_objects_ready(python world)(objects world)before->gateway_rooted(python world)(objects world)pointer->
  gateway_private_tree(objects world)pointer->gateway_destructible(objects world)pointer->
  gateway_held_description_holds decimal_float(objects world)pointer description->
  gateway_object_operation backend gateway_api_incref[pointer]before world result after next observed->
  exists final,
    gateway_reference_apply(gateway_reference_mint owner pointer)(gateway_reference_valid ledger)=
      gateway_reference_valid final /\gateway_reference_ledger_well_formed final /\
    gateway_reference_counts_fit final(python next) /\
    gateway_reference_owns final owner(gateway_reference_next ledger)pointer /\
    gateway_reference_held python objects decimal_float final
      (held++[{|gateway_held_ticket:=gateway_reference_next ledger;gateway_held_object:=pointer;
        gateway_held_view:=description|}])next /\
    gateway_objects_ready(python next)(objects next)after /\
    python_incref_return(python world)pointer before(python next)after.
Proof.
  intros FORMED FIT VACANT HELD READY ROOT PRIVATE DESTROY DESCRIPTION OPERATION.
  assert(LIVE:python_live(python world)pointer)by(exact(proj1(proj2(proj1 READY))pointer ROOT)).
  destruct(gateway_runtime_incref_objects _ _ _ references _ _ _ _ _ _ _ READY LIVE OPERATION)
    as[RETURN[AFTER[FRAME[PRIVACY[VALUE PRIVATE_VALUE]]]]].
  destruct(gateway_reference_credit_mints ledger owner pointer(python world)(python next)FORMED FIT VACANT
    (gateway_incref_reference_credit _ _ _ _ _ RETURN))
    as[final[MINT[WELL[COUNTS[OWNED RETAINED]]]]].
  assert(NEXT_ROOT:gateway_rooted(python next)(objects next)pointer)
    by(eapply gateway_reference_owned_rooted;[exact COUNTS|exact OWNED]).
  destruct(gateway_private_tree_preserved _ _ _ _ _ PRIVATE DESTROY ROOT NEXT_ROOT FRAME PRIVACY)
    as[NEXT_PRIVATE NEXT_DESTROY].
  assert(NEXT_DESCRIPTION:gateway_held_description_holds decimal_float(objects next)pointer description).
  { destruct description as[wire|scalar|wire initial];cbn in DESCRIPTION|-*.
    - eapply gateway_value_heap_retained;eassumption.
    - destruct DESCRIPTION as[LOOKUP CHILDREN];split;[|exact CHILDREN].
      eapply FRAME;[exact ROOT|exact NEXT_ROOT|apply PRIVATE;constructor|intro BAD;inversion BAD|exact LOOKUP].
    - destruct DESCRIPTION as[WIRE[INITIAL SNAPSHOT]];split.
      + eapply gateway_value_heap_retained;eassumption.
      + split;[exact INITIAL|]. eapply(gateway_graph_snapshot_retained(python world)(objects world)(python next)(objects next)initial pointer);
          [exact PRIVATE|exact DESTROY|exact ROOT|exact NEXT_ROOT|exact FRAME|exact PRIVACY|exact SNAPSHOT]. }
  exists final;split;[exact MINT|]. split;[exact WELL|]. split;[exact COUNTS|]. split;[exact OWNED|]. split.
  - apply Forall_app;split.
    + eapply gateway_reference_held_frame;[exact HELD|exact FIT|exact COUNTS| |exact FRAME|exact PRIVACY].
      intros captured MEMBER;pose proof(proj1(Forall_forall _ _)HELD captured MEMBER)as[[place OLD]REST].
      exists place;apply RETAINED;exact OLD.
    + constructor;[|constructor].
      exact(conj(ex_intro _ owner OWNED)(conj NEXT_PRIVATE(conj NEXT_DESTROY NEXT_DESCRIPTION))).
  - split;assumption.
Qed.

Theorem gateway_public_release_keeps_independent_graphs {World Event}(backend:gateway_backend World Event)
    python objects decimal_float(references:gateway_public_reference_runtime backend python objects)
    ledger owner ticket pointer held before world result after next observed:
  gateway_reference_ledger_well_formed ledger->gateway_reference_counts_fit ledger(python world)->
  gateway_reference_owns ledger owner ticket pointer->gateway_objects_attached(python world)(objects world)before->
  gateway_reference_held python objects decimal_float ledger held world->
  (forall captured,In captured held->gateway_held_ticket captured<>ticket)->
  gateway_object_operation backend gateway_api_decref[pointer]before world result after next observed->
  exists final,
    gateway_reference_apply(gateway_reference_release owner pointer)(gateway_reference_valid ledger)=
      gateway_reference_valid final /\gateway_reference_ledger_well_formed final /\
    gateway_reference_counts_fit final(python next) /\gateway_reference_held python objects decimal_float final held next /\
    gateway_attached_reference_return(python world)(objects world)before pointer(python next)(objects next)after /\
    (forall place other value,other<>ticket->gateway_reference_owns ledger place other value->
      gateway_reference_owns final place other value).
Proof.
  intros WELL FIT OWNED READY HELD DIFFERENT OPERATION.
  destruct(gateway_public_owned_release backend python objects references ledger owner ticket pointer
    before world result after next observed WELL FIT OWNED READY OPERATION)
    as(final &RELEASE &FINAL_WELL &COUNTS &RETURN &RETAINED).
  exists final;split;[exact RELEASE|]. split;[exact FINAL_WELL|]. split;[exact COUNTS|]. split;[|split;[exact RETURN|exact RETAINED]].
  eapply gateway_reference_held_frame;[exact HELD|exact FIT|exact COUNTS| | |].
  - intros captured MEMBER;pose proof(proj1(Forall_forall _ _)HELD captured MEMBER)as[[place OLD]REST].
    exists place;apply RETAINED;[apply DIFFERENT;exact MEMBER|exact OLD].
  - exact(gateway_attached_reference_values _ _ _ _ _ _ _ RETURN).
  - exact(gateway_attached_reference_privacy _ _ _ _ _ _ _ RETURN).
Qed.
