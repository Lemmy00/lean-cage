(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Reference cleanup retains a pending exception and source-native roots. *)
From Stdlib Require Import List Lia.
From compcert Require Import Values Memory.
From HostGateway Require Import GatewayMachine GatewayPython GatewayObjects GatewayReferences
  GatewayReferenceLedger GatewayReferenceAccounting.
Import ListNotations.

Definition gateway_objects_attached python heap memory:Prop:=
  gateway_objects_valid python heap memory /\python_gil python=true.

Record gateway_attached_reference_return python heap before pointer next next_heap after:Prop:={
  gateway_attached_reference_ready:gateway_objects_attached next next_heap after;
  gateway_attached_reference_pending:python_pending next=python_pending python;
  gateway_attached_reference_owned:python_native_strong python pointer=S(python_native_strong next pointer);
  gateway_attached_reference_others:gateway_native_references_frame python next[pointer];
  gateway_attached_reference_values:gateway_objects_frame python heap next next_heap[];
  gateway_attached_reference_privacy:gateway_object_privacy_frame python heap next next_heap[];
  gateway_attached_reference_native:python_private_frame python before after;
  gateway_attached_reference_native_retained:forall object,Mem.valid_block before object->
    gateway_native_private python object->gateway_native_private next object
}.

Record gateway_attached_reference_runtime {World Event}(backend:gateway_backend World Event)
    (python:World->python_world)(objects:World->gateway_object_heap):Prop:={
  gateway_attached_incref:forall before world pointer result after next observed,
    gateway_objects_attached(python world)(objects world)before->python_live(python world)pointer->
    gateway_object_operation backend gateway_api_incref[pointer]before world result after next observed->
    python_incref_return(python world)pointer before(python next)after /\
    gateway_objects_attached(python next)(objects next)after /\
    gateway_objects_frame(python world)(objects world)(python next)(objects next)[] /\
    gateway_object_privacy_frame(python world)(objects world)(python next)(objects next)[] /\
    gateway_object_values(objects next)pointer=gateway_object_values(objects world)pointer /\
    gateway_object_private(objects next)pointer=gateway_object_private(objects world)pointer;
  gateway_attached_decref:forall before world pointer result after next observed,
    gateway_objects_attached(python world)(objects world)before->
    (0<python_native_strong(python world)pointer)%nat->gateway_destructible(objects world)pointer->
    gateway_object_operation backend gateway_api_decref[pointer]before world result after next observed->
    gateway_attached_reference_return(python world)(objects world)before pointer(python next)(objects next)after
}.

Lemma gateway_normal_attached python heap memory:
  gateway_objects_ready python heap memory->gateway_objects_attached python heap memory.
Proof. intros[VALID[GIL CLEAR]];split;assumption. Qed.

Theorem gateway_attached_normal_references {World Event}(backend:gateway_backend World Event)python objects
    (runtime:gateway_attached_reference_runtime backend python objects):
  gateway_reference_runtime backend python objects.
Proof.
  constructor.
  - intros before world pointer result after next observed READY LIVE OPERATION.
    destruct(gateway_attached_incref _ _ _ runtime _ _ _ _ _ _ _
      (gateway_normal_attached _ _ _ READY)LIVE OPERATION)
      as[RETURN[[VALID GIL][FRAME[PRIVACY[VALUE PRIVATE]]]]].
    split;[exact RETURN|]. split.
    + split;[exact VALID|]. split;[exact GIL|].
      rewrite(python_incref_pending _ _ _ _ _ RETURN);exact(proj2(proj2 READY)).
    + exact(conj FRAME(conj PRIVACY(conj VALUE PRIVATE))).
  - intros before world pointer result after next observed READY POSITIVE DESTRUCTIBLE OPERATION.
    pose proof(gateway_attached_decref _ _ _ runtime _ _ _ _ _ _ _
      (gateway_normal_attached _ _ _ READY)POSITIVE DESTRUCTIBLE OPERATION)as RETURN.
    constructor.
    + destruct(gateway_attached_reference_ready _ _ _ _ _ _ _ RETURN)as[VALID GIL].
      split;[exact VALID|]. split;[exact GIL|].
      rewrite(gateway_attached_reference_pending _ _ _ _ _ _ _ RETURN);exact(proj2(proj2 READY)).
    + exact(gateway_attached_reference_owned _ _ _ _ _ _ _ RETURN).
    + exact(gateway_attached_reference_others _ _ _ _ _ _ _ RETURN).
    + exact(gateway_attached_reference_values _ _ _ _ _ _ _ RETURN).
    + exact(gateway_attached_reference_privacy _ _ _ _ _ _ _ RETURN).
    + exact(gateway_attached_reference_native _ _ _ _ _ _ _ RETURN).
    + exact(gateway_attached_reference_native_retained _ _ _ _ _ _ _ RETURN).
Qed.

Theorem gateway_attached_operand_release {World Event}(backend:gateway_backend World Event)python objects
    (runtime:gateway_attached_reference_runtime backend python objects)
    ledger owner ticket pointer before world result after next observed:
  gateway_reference_ledger_well_formed ledger->gateway_reference_counts_fit ledger(python world)->
  gateway_reference_owns ledger owner ticket pointer->
  gateway_objects_attached(python world)(objects world)before->gateway_destructible(objects world)pointer->
  gateway_object_operation backend gateway_api_decref[pointer]before world result after next observed->
  exists final,
    gateway_reference_apply(gateway_reference_release owner pointer)(gateway_reference_valid ledger)=
      gateway_reference_valid final /\gateway_reference_ledger_well_formed final /\
    gateway_reference_counts_fit final(python next) /\
    gateway_attached_reference_return(python world)(objects world)before pointer(python next)(objects next)after /\
    (forall place other value,other<>ticket->gateway_reference_owns ledger place other value->
      gateway_reference_owns final place other value).
Proof.
  intros FORMED FIT OWNED ATTACHED DESTRUCTIBLE OPERATION.
  assert(POSITIVE:(0<python_native_strong(python world)pointer)%nat).
  { pose proof(gateway_reference_owned_count_positive _ _ _ _ OWNED);specialize(FIT pointer);lia. }
  pose proof(gateway_attached_decref _ _ _ runtime _ _ _ _ _ _ _ ATTACHED POSITIVE DESTRUCTIBLE OPERATION)as RETURN.
  destruct(gateway_reference_release_counts ledger owner ticket pointer(python world)(python next)
    FORMED FIT OWNED(gateway_attached_reference_owned _ _ _ _ _ _ _ RETURN))
    as[final[APPLY[WELL[COUNTS RETAINED]]]].
  - intros other DIFFERENT;apply(gateway_attached_reference_others _ _ _ _ _ _ _ RETURN).
    intros[HEAD|TAIL];[congruence|contradiction].
  - exists final;exact(conj APPLY(conj WELL(conj COUNTS(conj RETURN RETAINED)))).
Qed.
