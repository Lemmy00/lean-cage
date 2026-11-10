(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Public-object cleanup keeps selected private roots, not mutable presentation. *)
From Stdlib Require Import List Lia.
From compcert Require Import Values Memory.
From HostGateway Require Import GatewayMachine GatewayPython GatewayObjects GatewayAttachedReferences
  GatewayReferenceLedger GatewayReferenceAccounting.
Import ListNotations.

(* Ordinary finalizers may mutate reachable public objects and reenter the
   application. Only the current source pool and independently private graphs
   have frames; no public value or full interpreter refcount is frozen. *)
Record gateway_public_reference_runtime {World Event}(backend:gateway_backend World Event)
    (python:World->python_world)(objects:World->gateway_object_heap):Prop:={
  gateway_public_decref:forall before world pointer result after next observed,
    gateway_objects_attached(python world)(objects world)before->
    (0<python_native_strong(python world)pointer)%nat->python_live(python world)pointer->
    gateway_object_operation backend gateway_api_decref[pointer]before world result after next observed->
    gateway_attached_reference_return(python world)(objects world)before pointer(python next)(objects next)after
}.

Theorem gateway_public_owned_release {World Event}(backend:gateway_backend World Event)python objects
    (runtime:gateway_public_reference_runtime backend python objects)
    ledger owner ticket pointer before world result after next observed:
  gateway_reference_ledger_well_formed ledger->gateway_reference_counts_fit ledger(python world)->
  gateway_reference_owns ledger owner ticket pointer->
  gateway_objects_attached(python world)(objects world)before->
  gateway_object_operation backend gateway_api_decref[pointer]before world result after next observed->
  exists final,
    gateway_reference_apply(gateway_reference_release owner pointer)(gateway_reference_valid ledger)=
      gateway_reference_valid final /\gateway_reference_ledger_well_formed final /\
    gateway_reference_counts_fit final(python next) /\
    gateway_attached_reference_return(python world)(objects world)before pointer(python next)(objects next)after /\
    (forall place other value,other<>ticket->gateway_reference_owns ledger place other value->
      gateway_reference_owns final place other value).
Proof.
  intros FORMED FIT OWNED ATTACHED OPERATION.
  assert(ROOT:gateway_rooted(python world)(objects world)pointer).
  { eapply gateway_reference_owned_rooted;[exact FIT|exact OWNED]. }
  assert(LIVE:python_live(python world)pointer).
  { destruct ATTACHED as[VALID GIL];exact(proj1(proj2 VALID)pointer ROOT). }
  assert(POSITIVE:(0<python_native_strong(python world)pointer)%nat).
  { pose proof(gateway_reference_owned_count_positive _ _ _ _ OWNED);specialize(FIT pointer);lia. }
  pose proof(gateway_public_decref _ _ _ runtime _ _ _ _ _ _ _ ATTACHED POSITIVE LIVE OPERATION)as RETURN.
  destruct(gateway_reference_release_counts ledger owner ticket pointer(python world)(python next)
    FORMED FIT OWNED(gateway_attached_reference_owned _ _ _ _ _ _ _ RETURN))
    as[final[APPLY[WELL[COUNTS RETAINED]]]].
  - intros other DIFFERENT;apply(gateway_attached_reference_others _ _ _ _ _ _ _ RETURN).
    intros[HEAD|TAIL];[congruence|contradiction].
  - exists final;exact(conj APPLY(conj WELL(conj COUNTS(conj RETURN RETAINED)))).
Qed.
