(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual allocation/store/return adopts the real copy credit
   into the same data cell and binds its returned instance credit to the actual caller. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayObjectDiscipline GatewayObjectThreads
  GatewayTypeRuntime GatewayReferenceRuntime GatewayOutcome GatewayOutcomeAllocation GatewayOutcomeConstruction GatewayOwnedOutcomeReturn
  GatewayOwnedOutcomeFactory GatewayReferenceBalance GatewayOwnedOutcomeAdoption GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting
  GatewayReferenceThreads GatewayReferenceNormalForm GatewayReferenceStackBound GatewayPermissionRuntime GatewayThreadRuntime GatewayStreamInterface GatewayObjectEvents GatewayLocalRuntime.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Theorem gateway_actual_owned_outcome_with_view {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects types allocator instances leases owned decimal_float detached io stable thread_errno heap_allocation normal
    (runtime:gateway_thread_runtime backend io(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (lifetimes:gateway_allocation_lifetime_runtime backend)
    (allocations:gateway_outcome_allocation_runtime backend python objects types allocator instances leases owned io
      (fun current object=>gateway_native_private(python current)object)stable)
    (type_references:gateway_type_reference_runtime backend python objects types allocator normal)
    (reference_threads:gateway_reference_thread_contract backend(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (view:World->Prop)(view_frame:forall before next,view before->gateway_reference_thread_effect python objects before next->view next)
    (reserved:list Values.val)
    context older ledger copy_ticket held environment parameters class description data_block data_offset before world events value after next descriptor:
  gateway_direct_io_projection backend io->gateway_outcome_member_layout ge->parameters!_copy=Some(Vptr data_block data_offset)->
  gateway_reference_stack_bound context older->gateway_reference_ledger_well_formed ledger->
  gateway_reference_entries ledger=gateway_reference_entry copy_ticket
    (gateway_reference_temporary(gateway_reference_depth context)_copy)(Vptr data_block data_offset)::gateway_reference_entries older->
  gateway_source_outcome_type description->gateway_type_basicsize description=24->gateway_type_itemsize description=0->
  Int.and(gateway_type_flags description)(Int.repr 256)=Int.repr 256->
  gateway_owned_outcome_class_context python objects types allocator decimal_float environment class description ledger held before world->view world->
  (forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count ledger pointer<=python_native_strong(python world)pointer)%nat)->
  gateway_steps backend ge
    (gateway_live(Callstate(External(EF_external "PyType_GenericAlloc"(mksignature[Xptr;Xlong]Xptr cc_default))
      [tptr(Tstruct __typeobject noattr);tlong](tptr(Tstruct __object noattr))cc_default)
      [class;Vlong Int64.zero](gateway_outcome_allocation_cont environment parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  exists object final,
    value=Vptr object Ptrofs.zero /\~Mem.valid_block before object /\gateway_reference_ledger_well_formed final /\
    gateway_reference_entries final=
      gateway_reference_entry(gateway_reference_next ledger)(gateway_reference_result(gateway_reference_depth context))value::
      gateway_reference_entry copy_ticket(gateway_reference_cell object 16)(Vptr data_block data_offset)::gateway_reference_entries older /\
    gateway_reference_source_bound ge(Returnstate value context after)final /\
    gateway_owned_outcome_return_context python objects instances owned decimal_float object(Vptr data_block data_offset)class final
      (gateway_reference_result(gateway_reference_depth context))(gateway_reference_next ledger)held after next /\
    gateway_reference_owns final(gateway_reference_cell object 16)copy_ticket(Vptr data_block data_offset) /\
    gateway_received_bytes io descriptor events=[] /\view next /\
    gateway_reference_balance(python world)(python next)ledger final /\
    (forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count final pointer<=python_native_strong(python next)pointer)%nat).
Proof.
  intros PROJECTION LAYOUT COPY STACK WELL COPY_ENTRIES ROLE SIZE ITEMS IMMUTABLE INPUT VIEW BUDGET RUN NONNULL.
  assert(VACANT:gateway_reference_take(gateway_reference_result(S(gateway_reference_depth context)))(gateway_reference_entries ledger)=None).
  { apply gateway_reference_take_none;intros entry MEMBER OWNER;rewrite COPY_ENTRIES in MEMBER.
    destruct MEMBER as[SAME|MEMBER];[subst entry;discriminate|].
    destruct(STACK entry MEMBER)as[depth[identifier[TEMP SAVED]]];congruence. }
  destruct(gateway_actual_outcome_allocation_keeps_view backend ge python objects types allocator instances leases owned decimal_float detached io stable
    thread_errno heap_allocation normal runtime lifetimes allocations type_references reference_threads view view_frame context environment parameters class description ledger held
    data_block data_offset before world events value after next descriptor PROJECTION LAYOUT COPY WELL VACANT ROLE SIZE ITEMS IMMUTABLE INPUT VIEW RUN NONNULL)
    as(object &minted &POINTER &FRESH &MINTED_WELL &MINT &RETURN_CONTEXT &EMPTY &FINAL_VIEW &BALANCE).
  pose proof(proj1(gateway_reference_mint_entries ledger minted(gateway_reference_result(S(gateway_reference_depth context)))value MINT))as MINTED_ENTRIES.
  rewrite COPY_ENTRIES,POINTER in MINTED_ENTRIES.
  destruct RETURN_CONTEXT as[NORMAL[CELL[LOAD[CLASS[OWNER SCOPE]]]]].
  destruct(gateway_owned_outcome_adopt_credits python objects decimal_float context older minted held next object(Vptr data_block data_offset)
    (gateway_reference_next ledger)copy_ticket STACK MINTED_WELL MINTED_ENTRIES SCOPE)
    as(adopted &final &ADOPT &RETURN &FINAL_WELL &FINAL_ENTRIES &FINAL_OWNER &FINAL_COPY &FINAL_SCOPE &COUNTS).
  exists object,final;split;[exact POINTER|]. split;[exact FRESH|]. split;[exact FINAL_WELL|]. split;
    [rewrite POINTER;exact FINAL_ENTRIES|]. split.
  - intros entry MEMBER;rewrite FINAL_ENTRIES in MEMBER.
    destruct MEMBER as[SAME|[SAME|MEMBER]].
    + subst entry;rewrite POINTER;apply gateway_reference_result_binding.
    + subst entry;exact LOAD.
    + destruct(STACK entry MEMBER)as[depth[identifier[TEMP SAVED]]];rewrite TEMP;exact SAVED.
  - split;[exact(conj NORMAL(conj CELL(conj LOAD(conj CLASS(conj FINAL_OWNER FINAL_SCOPE)))))|].
    split;[exact FINAL_COPY|]. split;[exact EMPTY|]. split;[exact FINAL_VIEW|].
    assert(FINAL_BALANCE:gateway_reference_balance(python world)(python next)ledger final).
    { intro pointer;rewrite COUNTS;apply BALANCE. }
    split;[exact FINAL_BALANCE|].
    eapply gateway_reference_balance_reservations;[exact BUDGET|exact FINAL_BALANCE].
Qed.


Theorem gateway_actual_owned_outcome {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects types allocator instances leases owned decimal_float detached io stable thread_errno heap_allocation normal
    (runtime:gateway_thread_runtime backend io(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (lifetimes:gateway_allocation_lifetime_runtime backend)
    (allocations:gateway_outcome_allocation_runtime backend python objects types allocator instances leases owned io
      (fun current object=>gateway_native_private(python current)object)stable)
    (type_references:gateway_type_reference_runtime backend python objects types allocator normal)
    (reference_threads:gateway_reference_thread_contract backend(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    context older ledger copy_ticket held environment parameters class description data_block data_offset before world events value after next descriptor:
  gateway_direct_io_projection backend io->gateway_outcome_member_layout ge->parameters!_copy=Some(Vptr data_block data_offset)->
  gateway_reference_stack_bound context older->gateway_reference_ledger_well_formed ledger->
  gateway_reference_entries ledger=gateway_reference_entry copy_ticket
    (gateway_reference_temporary(gateway_reference_depth context)_copy)(Vptr data_block data_offset)::gateway_reference_entries older->
  gateway_source_outcome_type description->gateway_type_basicsize description=24->gateway_type_itemsize description=0->
  Int.and(gateway_type_flags description)(Int.repr 256)=Int.repr 256->
  gateway_owned_outcome_class_context python objects types allocator decimal_float environment class description ledger held before world->
  gateway_steps backend ge
    (gateway_live(Callstate(External(EF_external "PyType_GenericAlloc"(mksignature[Xptr;Xlong]Xptr cc_default))
      [tptr(Tstruct __typeobject noattr);tlong](tptr(Tstruct __object noattr))cc_default)
      [class;Vlong Int64.zero](gateway_outcome_allocation_cont environment parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  exists object final,
    value=Vptr object Ptrofs.zero /\~Mem.valid_block before object /\gateway_reference_ledger_well_formed final /\
    gateway_reference_entries final=
      gateway_reference_entry(gateway_reference_next ledger)(gateway_reference_result(gateway_reference_depth context))value::
      gateway_reference_entry copy_ticket(gateway_reference_cell object 16)(Vptr data_block data_offset)::gateway_reference_entries older /\
    gateway_reference_source_bound ge(Returnstate value context after)final /\
    gateway_owned_outcome_return_context python objects instances owned decimal_float object(Vptr data_block data_offset)class final
      (gateway_reference_result(gateway_reference_depth context))(gateway_reference_next ledger)held after next /\
    gateway_reference_owns final(gateway_reference_cell object 16)copy_ticket(Vptr data_block data_offset) /\
    gateway_received_bytes io descriptor events=[].
Proof.
  intros PROJECTION LAYOUT COPY STACK WELL COPY_ENTRIES ROLE SIZE ITEMS IMMUTABLE INPUT RUN NONNULL.
  pose proof INPUT as[NORMAL[TYPE[ALLOCATOR[ROOT[SCOPE ENVIRONMENT]]]]].
  assert(BUDGET:forall pointer,(count_occ Val.eq []pointer+gateway_reference_count ledger pointer<=python_native_strong(python world)pointer)%nat).
  { intro pointer;cbn;exact(proj1 SCOPE pointer). }
  destruct(gateway_actual_owned_outcome_with_view backend ge python objects types allocator instances leases owned decimal_float detached io stable
    thread_errno heap_allocation normal runtime lifetimes allocations type_references reference_threads(fun _=>True)ltac:(intros;exact I)[]
    context older ledger copy_ticket held environment parameters class description data_block data_offset before world events value after next descriptor
    PROJECTION LAYOUT COPY STACK WELL COPY_ENTRIES ROLE SIZE ITEMS IMMUTABLE INPUT I BUDGET RUN NONNULL)
    as(object &final &POINTER &FRESH &FORMED &ENTRIES &BOUND &CONTEXT &OWNER &EMPTY &VIEW &BALANCE &RESERVATIONS).
  exists object,final;exact(conj POINTER(conj FRESH(conj FORMED(conj ENTRIES(conj BOUND(conj CONTEXT(conj OWNER EMPTY))))))).
Qed.
