(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Copy construction retains the aggregate captured and retired reference budget. *)
From Stdlib Require Import List Lia.
From compcert Require Import Values Memory.
From HostGateway Require Import GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayObjectThreads
  GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceRuntime GatewayReferenceHeld GatewayReferenceNormalForm GatewayOwnedOutcomeCopy.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_actual_private_outcome_copy_pool {World Event}(backend:gateway_backend World Event)
    python objects decimal_float(constructors:gateway_objects_runtime backend python objects decimal_float)
    ledger owner held reserved original fields before world result after next observed:
  gateway_reference_ledger_well_formed ledger->
  (forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count ledger pointer<=
    python_native_strong(python world)pointer)%nat)->
  gateway_reference_take owner(gateway_reference_entries ledger)=None->
  gateway_reference_held python objects decimal_float ledger held world->
  gateway_objects_ready(python world)(objects world)before->gateway_rooted(python world)(objects world)original->
  gateway_object_values(objects world)original=Some(gateway_dict_object fields)->gateway_object_private(objects world)original=true->
  gateway_object_operation backend gateway_api_dict_copy[original]before world result after next observed->result<>Vnullptr->
  exists final,
    gateway_reference_apply(gateway_reference_mint owner result)(gateway_reference_valid ledger)=gateway_reference_valid final /\
    gateway_reference_ledger_well_formed final /\
    gateway_reference_owns final owner(gateway_reference_next ledger)result /\
    gateway_reference_held python objects decimal_float final held next /\
    (forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count final pointer<=
      python_native_strong(python next)pointer)%nat) /\
    gateway_constructor_return(python world)(objects world)before result(python next)(objects next)after(gateway_dict_object fields).
Proof.
  intros WELL BUDGET VACANT HELD READY ROOT VALUE PRIVATE OPERATION NONNULL.
  assert(FIT:gateway_reference_counts_fit ledger(python world)).
  { intro pointer;specialize(BUDGET pointer);lia. }
  destruct(gateway_actual_private_outcome_copy backend python objects decimal_float constructors ledger owner held original fields
    before world result after next observed WELL FIT VACANT HELD READY ROOT VALUE PRIVATE OPERATION NONNULL)
    as(final &MINT &FINAL_WELL &COUNTS &OWNED &FINAL_HELD &RETURN &RETAINED).
  pose proof(proj1(gateway_reference_mint_entries ledger final owner result MINT))as ENTRIES.
  pose proof(gateway_constructor_reference_credit _ _ _ _ _ _ _ _ RETURN)as CREDIT.
  exists final;split;[exact MINT|]. split;[exact FINAL_WELL|]. split;[exact OWNED|]. split;[exact FINAL_HELD|]. split;[|exact RETURN].
  intro pointer;unfold gateway_reference_count;rewrite ENTRIES;cbn[gateway_reference_entry gateway_reference_pointer map count_occ].
  specialize(BUDGET pointer);unfold gateway_reference_count in BUDGET.
  destruct(Val.eq result pointer)as[SAME|DIFFERENT].
  - subst pointer;rewrite(gateway_reference_credit_target _ _ _ CREDIT);lia.
  - rewrite(gateway_reference_credit_other _ _ _ CREDIT pointer ltac:(congruence));exact BUDGET.
Qed.
