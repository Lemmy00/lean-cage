(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The original class load, data store and return retain the received observations. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayObjectDiscipline GatewayObjectThreads
  GatewayTypeRuntime GatewayReferenceRuntime GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting GatewayReferenceNormalForm
  GatewayReferenceStackBound GatewayReferenceBalance GatewayReferenceThreads GatewayOwnedOutcomeFactory GatewayOwnedOutcomeReturn GatewayOwnedOutcome
  GatewayOutcome GatewayOutcomeAllocation GatewayOutcomeConstruction GatewayOutcomeMetadata GatewayOutcomeFields GatewayObjectEvents
  GatewayOutcomeAllocationEntry GatewayOutcomeReceivedReturn GatewaySourcePaths GatewayFramedRuntime GatewayPermissionRuntime
  GatewayThreadRuntime GatewayStreamInterface.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_actual_received_outcome_construction {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects types allocator instances leases owned decimal_float detached io stable thread_errno heap_allocation normal
    (runtime:gateway_thread_runtime backend io(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (lifetimes:gateway_allocation_lifetime_runtime backend)
    (allocations:gateway_outcome_allocation_runtime backend python objects types allocator instances leases owned io
      (fun current object=>gateway_native_private(python current)object)stable)
    (type_references:gateway_type_reference_runtime backend python objects types allocator normal)
    (reference_threads:gateway_reference_thread_contract backend(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    context older ledger copy_ticket held reserved environment parameters class class_offset description copy copy_offset fields wires metadata_field metadata wire
    before world events value after next(descriptor:int)class_symbol allocator_symbol:
  gateway_direct_io_projection backend io->gateway_outcome_member_layout ge->parameters!_copy=Some(Vptr copy copy_offset)->
  gateway_reference_stack_bound context older->gateway_reference_ledger_well_formed ledger->
  gateway_reference_entries ledger=gateway_reference_entry copy_ticket
    (gateway_reference_temporary(gateway_reference_depth context)_copy)(Vptr copy copy_offset)::gateway_reference_entries older->
  gateway_source_outcome_type description->gateway_type_basicsize description=24%Z->gateway_type_itemsize description=0%Z->
  Int.and(gateway_type_flags description)(Int.repr 256)=Int.repr 256->
  gateway_owned_outcome_class_context python objects types allocator decimal_float environment(Vptr class class_offset)description ledger held before world->
  gateway_outcome_fields_view python objects decimal_float(Vptr copy copy_offset)fields wires world->
  gateway_outcome_metadata_view python objects decimal_float(Vptr copy copy_offset)fields metadata_field metadata wire world->
  (forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count ledger pointer<=python_native_strong(python world)pointer)%nat)->
  environment!_host_outcome_class=None->environment!_PyType_GenericAlloc=None->
  Genv.find_symbol ge _host_outcome_class=Some class_symbol->Genv.find_symbol ge _PyType_GenericAlloc=Some allocator_symbol->
  Genv.find_funct_ptr ge allocator_symbol=Some gateway_outcome_allocator_definition->
  Mem.loadv Mptr before(Vptr class_symbol Ptrofs.zero)=Some(Vptr class class_offset)->
  (forall memory current changed following,gateway_objects_ready(python current)(objects current)memory->
    Mem.loadv Mptr memory(Vptr class_symbol Ptrofs.zero)=Some(Vptr class class_offset)->
    gateway_interference backend memory current changed following->
    Mem.loadv Mptr changed(Vptr class_symbol Ptrofs.zero)=Some(Vptr class class_offset))->
  gateway_steps backend ge
    (gateway_live(State f_host_outcome_from gateway_outcome_allocation_tail Kstop environment parameters before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  exists prefix suffix selected called current object final,
    events=prefix++suffix /\selected!_copy=Some(Vptr copy copy_offset) /\
    gateway_steps backend ge
      (gateway_live(State f_host_outcome_from gateway_outcome_allocation_tail Kstop environment parameters before)world)prefix
      (gateway_live(Callstate gateway_outcome_allocator_definition[Vptr class class_offset;Vlong Int64.zero]
        (gateway_outcome_allocation_cont environment selected)called)current) /\
    gateway_steps backend ge
      (gateway_live(Callstate gateway_outcome_allocator_definition[Vptr class class_offset;Vlong Int64.zero]
        (gateway_outcome_allocation_cont environment selected)called)current)suffix
      (gateway_live(Returnstate value Kstop after)next) /\
    value=Vptr object Ptrofs.zero /\~Mem.valid_block called object /\gateway_reference_ledger_well_formed final /\
    gateway_reference_entries final=gateway_reference_entry(gateway_reference_next ledger)
      (gateway_reference_result(gateway_reference_depth context))value::
      gateway_reference_entry copy_ticket(gateway_reference_cell object 16%Z)(Vptr copy copy_offset)::gateway_reference_entries older /\
    gateway_reference_source_bound ge(Returnstate value context after)final /\
    gateway_owned_outcome_return_context python objects instances owned decimal_float object(Vptr copy copy_offset)(Vptr class class_offset)final
      (gateway_reference_result(gateway_reference_depth context))(gateway_reference_next ledger)held after next /\
    gateway_reference_owns final(gateway_reference_cell object 16%Z)copy_ticket(Vptr copy copy_offset) /\
    gateway_outcome_fields_view python objects decimal_float(Vptr copy copy_offset)fields wires next /\
    gateway_outcome_metadata_view python objects decimal_float(Vptr copy copy_offset)fields metadata_field metadata wire next /\
    (forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count final pointer<=python_native_strong(python next)pointer)%nat).
Proof.
  intros PROJECTION LAYOUT COPY STACK WELL ENTRIES ROLE SIZE ITEMS IMMUTABLE INITIAL FIELDS METADATA BUDGET
    CLASS_LOCAL ALLOCATOR_LOCAL CLASS_SYMBOL ALLOCATOR_SYMBOL ALLOCATOR_FUNCTION LOAD RETAINED RUN NONNULL.
  set(property:=fun memory current=>
    gateway_owned_outcome_class_context python objects types allocator decimal_float environment(Vptr class class_offset)description ledger held memory current /\
    gateway_outcome_fields_view python objects decimal_float(Vptr copy copy_offset)fields wires current /\
    gateway_outcome_metadata_view python objects decimal_float(Vptr copy copy_offset)fields metadata_field metadata wire current /\
    (forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count ledger pointer<=python_native_strong(python current)pointer)%nat) /\
    Mem.loadv Mptr memory(Vptr class_symbol Ptrofs.zero)=Some(Vptr class class_offset)).
  assert(CLOSED:gateway_ambient_closed backend property).
  { intros memory current changed following[CONTEXT[FIELDS_NOW[META_NOW[BUDGET_NOW LOAD_NOW]]]]AMBIENT.
    pose proof(@gateway_reference_thread_ambient World Event backend(fun current object=>gateway_native_private(python current)object)
      stable(gateway_python_discipline python objects detached)heap_allocation python objects reference_threads None
      memory current changed following(proj1 CONTEXT)AMBIENT)as EFFECT.
    split.
    - eapply gateway_owned_outcome_class_context_ambient;[exact runtime|exact allocations|exact reference_threads|
        exact IMMUTABLE|exact CONTEXT|exact AMBIENT].
    - split;[eapply gateway_outcome_fields_view_frame;eassumption|].
      split;[eapply gateway_outcome_metadata_view_frame;eassumption|]. split.
      + intro pointer;specialize(BUDGET_NOW pointer);pose proof(gateway_reference_thread_counts _ _ _ _ EFFECT pointer);lia.
      + eapply RETAINED;[exact(proj1 CONTEXT)|exact LOAD_NOW|exact AMBIENT]. }
  destruct(gateway_outcome_allocation_source backend ge property environment parameters class class_offset before class_symbol allocator_symbol
    CLOSED CLASS_LOCAL ALLOCATOR_LOCAL CLASS_SYMBOL ALLOCATOR_SYMBOL ALLOCATOR_FUNCTION ltac:(intros memory current GOOD;exact(proj2(proj2(proj2(proj2 GOOD))))))
    as[selected[PATH[SELECTED_COPY[SELECTED_DATA SELECTED_CLASS]]]].
  destruct(gateway_source_path_cut backend ge gateway_outcome_allocator_definition[Vptr class class_offset;Vlong Int64.zero]
    (gateway_outcome_allocation_cont environment selected)property _ property PATH before world events value after next
    (conj INITIAL(conj FIELDS(conj METADATA(conj BUDGET LOAD))))RUN)
    as(prefix &suffix &called &current &EVENTS &QUIET &PREFIX &[AT_CALL[FIELD_CALL[META_CALL[BUDGET_CALL LOAD_CALL]]]]&SUFFIX).
  assert(COPY_CALL:selected!_copy=Some(Vptr copy copy_offset))by(rewrite SELECTED_COPY;exact COPY).
  destruct(gateway_actual_received_outcome_return backend ge python objects types allocator instances leases owned decimal_float detached io stable
    thread_errno heap_allocation normal runtime lifetimes allocations type_references reference_threads context older ledger copy_ticket held reserved
    environment selected(Vptr class class_offset)description copy copy_offset fields wires metadata_field metadata wire called current suffix value after next descriptor
    PROJECTION LAYOUT COPY_CALL STACK WELL ENTRIES ROLE SIZE ITEMS IMMUTABLE AT_CALL FIELD_CALL META_CALL BUDGET_CALL SUFFIX NONNULL)
    as(object &final &POINTER &FRESH &FINAL_WELL &FINAL_ENTRIES &SOURCE_BOUND &RETURN_CONTEXT &COPY_CELL &FINAL_FIELDS &FINAL_META &BALANCE &FINAL_BUDGET).
  exists prefix,suffix,selected,called,current,object,final.
  exact(conj EVENTS(conj COPY_CALL(conj PREFIX(conj SUFFIX(conj POINTER(conj FRESH(conj FINAL_WELL(conj FINAL_ENTRIES
    (conj SOURCE_BOUND(conj RETURN_CONTEXT(conj COPY_CELL(conj FINAL_FIELDS(conj FINAL_META FINAL_BUDGET))))))))))))).
Qed.
