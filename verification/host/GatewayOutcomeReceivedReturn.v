(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The same received field views reach the real Outcome data cell and caller result. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps AST Integers Values Memory Events Ctypes Ctypesdefs Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayObjectDiscipline GatewayObjectThreads
  GatewayTypeRuntime GatewayReferenceRuntime GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting GatewayReferenceNormalForm
  GatewayReferenceStackBound GatewayReferenceBalance GatewayReferenceThreads GatewayOwnedOutcomeFactory GatewayOwnedOutcomeReturn GatewayOwnedOutcome
  GatewayOutcome GatewayOutcomeAllocation GatewayOutcomeConstruction GatewayOutcomeMetadata GatewayOutcomeFields GatewayObjectEvents
  GatewayPermissionRuntime GatewayThreadRuntime GatewayStreamInterface.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_actual_received_outcome_return {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects types allocator instances leases owned decimal_float detached io stable thread_errno heap_allocation normal
    (runtime:gateway_thread_runtime backend io(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (lifetimes:gateway_allocation_lifetime_runtime backend)
    (allocations:gateway_outcome_allocation_runtime backend python objects types allocator instances leases owned io
      (fun current object=>gateway_native_private(python current)object)stable)
    (type_references:gateway_type_reference_runtime backend python objects types allocator normal)
    (reference_threads:gateway_reference_thread_contract backend(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    context older ledger copy_ticket held reserved environment parameters class description copy copy_offset fields wires metadata_field metadata wire
    before world events value after next(descriptor:int):
  gateway_direct_io_projection backend io->gateway_outcome_member_layout ge->parameters!_copy=Some(Vptr copy copy_offset)->
  gateway_reference_stack_bound context older->gateway_reference_ledger_well_formed ledger->
  gateway_reference_entries ledger=gateway_reference_entry copy_ticket
    (gateway_reference_temporary(gateway_reference_depth context)_copy)(Vptr copy copy_offset)::gateway_reference_entries older->
  gateway_source_outcome_type description->gateway_type_basicsize description=24%Z->gateway_type_itemsize description=0%Z->
  Int.and(gateway_type_flags description)(Int.repr 256)=Int.repr 256->
  gateway_owned_outcome_class_context python objects types allocator decimal_float environment class description ledger held before world->
  gateway_outcome_fields_view python objects decimal_float(Vptr copy copy_offset)fields wires world->
  gateway_outcome_metadata_view python objects decimal_float(Vptr copy copy_offset)fields metadata_field metadata wire world->
  (forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count ledger pointer<=python_native_strong(python world)pointer)%nat)->
  gateway_steps backend ge
    (gateway_live(Callstate(External(EF_external "PyType_GenericAlloc"(mksignature[Xptr;Xlong]Xptr cc_default))
      [tptr(Tstruct __typeobject noattr);tlong](tptr(Tstruct __object noattr))cc_default)
      [class;Vlong Int64.zero](gateway_outcome_allocation_cont environment parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  exists object final,
    value=Vptr object Ptrofs.zero /\~Mem.valid_block before object /\gateway_reference_ledger_well_formed final /\
    gateway_reference_entries final=gateway_reference_entry(gateway_reference_next ledger)
      (gateway_reference_result(gateway_reference_depth context))value::
      gateway_reference_entry copy_ticket(gateway_reference_cell object 16%Z)(Vptr copy copy_offset)::gateway_reference_entries older /\
    gateway_reference_source_bound ge(Returnstate value context after)final /\
    gateway_owned_outcome_return_context python objects instances owned decimal_float object(Vptr copy copy_offset)class final
      (gateway_reference_result(gateway_reference_depth context))(gateway_reference_next ledger)held after next /\
    gateway_reference_owns final(gateway_reference_cell object 16%Z)copy_ticket(Vptr copy copy_offset) /\
    gateway_outcome_fields_view python objects decimal_float(Vptr copy copy_offset)fields wires next /\
    gateway_outcome_metadata_view python objects decimal_float(Vptr copy copy_offset)fields metadata_field metadata wire next /\
    gateway_reference_balance(python world)(python next)ledger final /\
    (forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count final pointer<=python_native_strong(python next)pointer)%nat).
Proof.
  intros PROJECTION LAYOUT COPY STACK WELL ENTRIES ROLE SIZE ITEMS IMMUTABLE INITIAL FIELDS METADATA BUDGET RUN NONNULL.
  set(view:=fun current=>gateway_outcome_fields_view python objects decimal_float(Vptr copy copy_offset)fields wires current /\
    gateway_outcome_metadata_view python objects decimal_float(Vptr copy copy_offset)fields metadata_field metadata wire current).
  assert(FRAME:forall first last,view first->gateway_reference_thread_effect python objects first last->view last).
  { intros first last[FIELD_VIEWS METADATA_VIEW]EFFECT;split.
    - eapply gateway_outcome_fields_view_frame;eassumption.
    - eapply gateway_outcome_metadata_view_frame;eassumption. }
  destruct(gateway_actual_owned_outcome_with_view backend ge python objects types allocator instances leases owned decimal_float detached io stable
    thread_errno heap_allocation normal runtime lifetimes allocations type_references reference_threads view FRAME reserved
    context older ledger copy_ticket held environment parameters class description copy copy_offset before world events value after next descriptor
    PROJECTION LAYOUT COPY STACK WELL ENTRIES ROLE SIZE ITEMS IMMUTABLE INITIAL(conj FIELDS METADATA)BUDGET RUN NONNULL)
    as(object &final &POINTER &FRESH &FINAL_WELL &FINAL_ENTRIES &BOUND &CONTEXT &CELL &EMPTY &[FINAL_FIELDS FINAL_METADATA]&BALANCE &FINAL_BUDGET).
  exists object,final;exact(conj POINTER(conj FRESH(conj FINAL_WELL(conj FINAL_ENTRIES(conj BOUND(conj CONTEXT(conj CELL
    (conj FINAL_FIELDS(conj FINAL_METADATA(conj BALANCE FINAL_BUDGET)))))))))).
Qed.
