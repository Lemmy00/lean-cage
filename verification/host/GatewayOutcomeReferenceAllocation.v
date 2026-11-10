(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual GenericAlloc creates an instance reference at its real return place. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayRuntime GatewayPython GatewayObjects
  GatewayTypeRuntime GatewayOutcomeAllocation GatewayOutcomeConstruction GatewayThreadRuntime GatewayStreamInterface
  GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting GatewayReferenceRuntime.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_actual_outcome_reference_alloc {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects types allocator instances leases owned io native stable normal
    (allocations:gateway_outcome_allocation_runtime backend python objects types allocator instances leases owned io native stable)
    (references:gateway_type_reference_runtime backend python objects types allocator normal)
    ledger class_place class_ticket class description environment parameters before world result after next observed:
  gateway_reference_ledger_well_formed ledger->gateway_reference_counts_fit ledger(python world)->
  gateway_reference_owns ledger class_place class_ticket class->
  gateway_reference_take(gateway_reference_result
    (gateway_reference_depth(gateway_outcome_allocation_cont environment parameters)))
    (gateway_reference_entries ledger)=None->
  gateway_objects_ready(python world)(objects world)before->gateway_source_outcome_type description->
  types world class=Some description->allocator world class->
  gateway_type_basicsize description=24->gateway_type_itemsize description=0->
  Int.and(gateway_type_flags description)(Int.repr 256)=Int.repr 256->
  gateway_step backend ge
    (gateway_live(Callstate(External(EF_external "PyType_GenericAlloc"(mksignature[Xptr;Xlong]Xptr cc_default))
      [tptr(Tstruct __typeobject noattr);tlong](tptr(Tstruct __object noattr))cc_default)
      [class;Vlong Int64.zero](gateway_outcome_allocation_cont environment parameters)before)world)
    (gateway_primitive observed)
    (gateway_live(Returnstate result(gateway_outcome_allocation_cont environment parameters)after)next)->result<>Vnullptr->
  exists final object,
    result=Vptr object Ptrofs.zero /\~Mem.valid_block before object /\
    gateway_objects_ready(python next)(objects next)after /\instances next result=Some class /\
    types next class=Some description /\allocator next class /\
    gateway_object_values(objects next)result=Some gateway_outcome_object /\
    gateway_object_private(objects next)result=true /\gateway_outcome_private_cell python owned after next object /\
    Mem.load Mptr after object 16=Some Vnullptr /\
    gateway_reference_apply(gateway_reference_mint(gateway_reference_result
      (gateway_reference_depth(gateway_outcome_allocation_cont environment parameters)))result)
      (gateway_reference_valid ledger)=gateway_reference_valid final /\
    gateway_reference_ledger_well_formed final /\gateway_reference_counts_fit final(python next) /\
    gateway_reference_owns final(gateway_reference_result
      (gateway_reference_depth(gateway_outcome_allocation_cont environment parameters)))
      (gateway_reference_next ledger)result /\
    gateway_reference_place_value ge(Returnstate result(gateway_outcome_allocation_cont environment parameters)after)
      (gateway_reference_result(gateway_reference_depth(gateway_outcome_allocation_cont environment parameters)))result /\
    (forall place ticket pointer,gateway_reference_owns ledger place ticket pointer->
      gateway_reference_owns final place ticket pointer).
Proof.
  intros FORMED FIT CLASS_OWNED VACANT READY TYPE_ROLE TYPE ALLOCATOR SIZE ITEMS IMMUTABLE STEP NONNULL.
  assert(ROOT:gateway_rooted(python world)(objects world)class).
  { eapply gateway_reference_owned_rooted;[exact FIT|exact CLASS_OWNED]. }
  assert(OPERATION:gateway_object_operation backend gateway_api_generic_alloc[class;Vlong Int64.zero]
    before world result after next observed).
  { eapply gateway_object_operation_actual;[exact actual_gateway_generic_alloc_abi|exact STEP]. }
  destruct(gateway_actual_generic_allocated backend python objects types allocator instances leases owned io native stable
    allocations before world class description result after next observed READY ROOT TYPE ALLOCATOR SIZE ITEMS IMMUTABLE
    OPERATION NONNULL)
    as(object&old_ticket&POINTER&FRESH&NEXT_READY&INSTANCE&NEXT_TYPE&NEXT_ALLOCATOR&VALUE&PRIVATE&OLD_LEASE&
      CELL&INITIALIZED&FRAME&PRIVACY).
  pose proof(@gateway_type_reference_generic_alloc World Event backend python objects types allocator normal references
    before world class description result after next observed READY TYPE_ROLE ROOT TYPE ALLOCATOR SIZE ITEMS IMMUTABLE
    OPERATION NONNULL)as CREDIT.
  destruct(gateway_reference_credit_mints ledger(gateway_reference_result
    (gateway_reference_depth(gateway_outcome_allocation_cont environment parameters)))result
    (python world)(python next)FORMED FIT VACANT CREDIT)
    as[final[APPLY[WELL[COUNTS[OWNED RETAINED]]]]].
  exists final,object;split;[exact POINTER|]. split;[exact FRESH|]. split;[exact NEXT_READY|].
  split;[exact INSTANCE|]. split;[exact NEXT_TYPE|]. split;[exact NEXT_ALLOCATOR|]. split;[exact VALUE|].
  split;[exact PRIVATE|]. split;[exact CELL|]. split;[exact INITIALIZED|]. split;[exact APPLY|].
  split;[exact WELL|]. split;[exact COUNTS|]. split;[exact OWNED|].
  split;[apply gateway_reference_result_binding|exact RETAINED].
Qed.
