(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual private copy creates one source credit without replacing metadata. *)
From Stdlib Require Import List.
From compcert Require Import Values Memory.
From HostGateway Require Import GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayValueOwnership
  GatewayObjectThreads GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceRuntime GatewayReferenceHeld GatewayReferenceRetained.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_actual_private_outcome_copy {World Event}(backend:gateway_backend World Event)
    python objects decimal_float(constructors:gateway_objects_runtime backend python objects decimal_float)
    ledger owner held original fields before world result after next observed:
  gateway_reference_ledger_well_formed ledger->gateway_reference_counts_fit ledger(python world)->
  gateway_reference_take owner(gateway_reference_entries ledger)=None->
  gateway_reference_held python objects decimal_float ledger held world->
  gateway_objects_ready(python world)(objects world)before->gateway_rooted(python world)(objects world)original->
  gateway_object_values(objects world)original=Some(gateway_dict_object fields)->
  gateway_object_private(objects world)original=true->
  gateway_object_operation backend gateway_api_dict_copy[original]before world result after next observed->result<>Vnullptr->
  exists final,
    gateway_reference_apply(gateway_reference_mint owner result)(gateway_reference_valid ledger)=gateway_reference_valid final /\
    gateway_reference_ledger_well_formed final /\gateway_reference_counts_fit final(python next) /\
    gateway_reference_owns final owner(gateway_reference_next ledger)result /\
    gateway_reference_held python objects decimal_float final held next /\
    gateway_constructor_return(python world)(objects world)before result(python next)(objects next)after(gateway_dict_object fields) /\
    (forall place ticket pointer,gateway_reference_owns ledger place ticket pointer->gateway_reference_owns final place ticket pointer).
Proof.
  intros WELL FIT VACANT HELD READY ROOT VALUE PRIVATE OPERATION NONNULL.
  assert(REQUEST:gateway_constructor_request decimal_float(objects world)before gateway_api_dict_copy[original](gateway_dict_object fields)).
  { apply gateway_request_dictionary_copy;assumption. }
  assert(ROOTS:gateway_constructor_roots(python world)(objects world)gateway_api_dict_copy[original]).
  { exact ROOT. }
  pose proof(gateway_runtime_constructor backend python objects decimal_float constructors _ _ _ _ _ _ _ _ _
    READY REQUEST ROOTS OPERATION NONNULL)as RETURN.
  destruct(gateway_reference_credit_mints ledger owner result(python world)(python next)WELL FIT VACANT
    (gateway_constructor_reference_credit _ _ _ _ _ _ _ _ RETURN))
    as(final &MINT &FINAL_WELL &COUNTS &OWNED &RETAINED).
  assert(FINAL_HELD:gateway_reference_held python objects decimal_float final held next).
  { destruct(gateway_constructor_all_private_frames _ _ _ _ _ _ _ _ RETURN)as[FRAME PRIVACY].
    eapply gateway_reference_held_frame;[exact HELD|exact FIT|exact COUNTS| |exact FRAME|exact PRIVACY].
    intros captured MEMBER;pose proof(proj1(Forall_forall _ _)HELD captured MEMBER)as[[place OLD]REST].
    exists place;apply RETAINED;exact OLD. }
  exists final;exact(conj MINT(conj FINAL_WELL(conj COUNTS(conj OWNED(conj FINAL_HELD(conj RETURN RETAINED)))))).
Qed.
