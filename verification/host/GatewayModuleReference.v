(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual FromSpec return mints one source-owned class reference. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayRuntime GatewayTypeRuntime GatewayPython
  GatewayObjects GatewayOutcomeType GatewayModuleSource GatewayModuleRegions GatewayReferenceLedger
  GatewayReferencePlaces GatewayReferenceAccounting GatewayReferenceRuntime.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_actual_module_type_reference {World Event}(backend:gateway_backend World Event)
    python objects types allocator instances leases normal attached io native stable
    (runtime:gateway_type_runtime backend python objects types allocator instances leases normal attached io native stable)
    (references:gateway_type_reference_runtime backend python objects types allocator normal)
    ledger before world specification new initialize destroy traverse clear methods properties
    temporaries continuation result after next observed:
  gateway_reference_ledger_well_formed ledger->gateway_reference_counts_fit ledger(python world)->
  gateway_reference_take(gateway_reference_result(gateway_reference_depth(module_outcome_cont temporaries continuation)))
    (gateway_reference_entries ledger)=None->normal before world->
  gateway_source_outcome_spec(Vptr specification Ptrofs.zero)->
  gateway_source_outcome_type(gateway_outcome_description new initialize destroy traverse clear methods properties)->
  gateway_type_spec_memory before(Vptr specification Ptrofs.zero)
    (gateway_outcome_description new initialize destroy traverse clear methods properties)->
  gateway_step backend(Clight.globalenv prog)
    (gateway_live(Callstate(External(EF_external "PyType_FromSpec"(mksignature[Xptr]Xptr cc_default))
      [tptr(Tstruct __5268 noattr)](tptr(Tstruct __object noattr))cc_default)
      [Vptr specification Ptrofs.zero](module_outcome_cont temporaries continuation)before)world)
    (gateway_primitive observed)(gateway_live(Returnstate result(module_outcome_cont temporaries continuation)after)next)->
  result<>Vnullptr->
  exists final object offset,
    result=Vptr object offset /\normal after next /\
    types next result=Some(gateway_outcome_description new initialize destroy traverse clear methods properties) /\
    allocator next result /\gateway_rooted(python next)(objects next)result /\
    gateway_reference_apply(gateway_reference_mint
      (gateway_reference_result(gateway_reference_depth(module_outcome_cont temporaries continuation)))result)
      (gateway_reference_valid ledger)=gateway_reference_valid final /\
    gateway_reference_ledger_well_formed final /\gateway_reference_counts_fit final(python next) /\
    gateway_reference_owns final
      (gateway_reference_result(gateway_reference_depth(module_outcome_cont temporaries continuation)))
      (gateway_reference_next ledger)result /\
    gateway_reference_place_value(Clight.globalenv prog)
      (Returnstate result(module_outcome_cont temporaries continuation)after)
      (gateway_reference_result(gateway_reference_depth(module_outcome_cont temporaries continuation)))result /\
    (forall place ticket pointer,gateway_reference_owns ledger place ticket pointer->
      gateway_reference_owns final place ticket pointer).
Proof.
  intros FORMED FIT VACANT NORMAL SPEC_ROLE TYPE_ROLE SPECIFICATION STEP NONNULL.
  assert(OPERATION:gateway_type_operation backend gateway_type_from_spec[Vptr specification Ptrofs.zero]
    before world result after next observed).
  { eexists;split;[reflexivity|]. inversion STEP;subst;cbn[gateway_runtime_operation];eassumption. }
  destruct(@gateway_type_from_spec_effect World Event backend python objects types allocator instances leases
    normal attached io native stable runtime before world(Vptr specification Ptrofs.zero)
    (gateway_outcome_description new initialize destroy traverse clear methods properties)result after next observed
    NORMAL SPECIFICATION ltac:(cbn;lia)eq_refl OPERATION)
    as[ATTACHED[ACCESS[FRAME[QUIET[NULL|[old_ticket[CLEAR[TYPE[DEFAULT OLD_CREATED]]]]]]]]];[contradiction|].
  pose proof(@gateway_type_reference_from_spec World Event backend python objects types allocator normal references
    before world(Vptr specification Ptrofs.zero)
    (gateway_outcome_description new initialize destroy traverse clear methods properties)result after next observed
    NORMAL SPEC_ROLE TYPE_ROLE SPECIFICATION ltac:(cbn;lia)eq_refl OPERATION NONNULL)as CREDIT.
  destruct(gateway_reference_credit_mints ledger
    (gateway_reference_result(gateway_reference_depth(module_outcome_cont temporaries continuation)))result
    (python world)(python next)FORMED FIT VACANT CREDIT)
    as[final[APPLY[WELL[COUNTS[OWNED RETAINED]]]]].
  assert(ROOT:gateway_rooted(python next)(objects next)result).
  { eapply gateway_reference_owned_rooted;[exact COUNTS|exact OWNED]. }
  destruct(@gateway_type_attached World Event backend python objects types allocator instances leases
    normal attached io native stable runtime after next ATTACHED)as[GIL VALID].
  destruct(proj2(proj2(proj2(proj2 VALID)))result ROOT)as[object[offset[POINTER LIVE]]].
  exists final,object,offset;split;[exact POINTER|]. split;[exact CLEAR|]. split;[exact TYPE|].
  split;[apply DEFAULT;apply gateway_outcome_allocator_is_default|]. split;[exact ROOT|].
  split;[exact APPLY|]. split;[exact WELL|]. split;[exact COUNTS|]. split;[exact OWNED|].
  split;[apply gateway_reference_result_binding|exact RETAINED].
Qed.
