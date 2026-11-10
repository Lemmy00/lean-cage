(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The same allocation call, field assignment and return own the Outcome data. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayOperations GatewayReadonly GatewayFramedRuntime
  GatewayObjects GatewayPython GatewayObjectDiscipline GatewayRootLeases GatewayObjectThreads GatewayTypeRuntime
  GatewayOutcome GatewayOutcomeAllocation GatewayOutcomeConstruction GatewayOutcomeReturn GatewayOutcomeResult
  GatewayOutcomeFailure GatewayLocalRuntime GatewayObjectEvents GatewayObjectRuns GatewayThreadRuntime GatewayStreamInterface GatewayPathEvents.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Section OutcomeFactory.
Context {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
  (python:World->python_world)(objects:World->gateway_object_heap)
  (types:World->Values.val->option gateway_type_description)(default_allocator:World->Values.val->Prop)
  (instances:World->Values.val->option Values.val)(leases:World->nat->Values.val->Prop)(owned:World->Values.val->Prop)
  (decimal_float:list Z->Floats.float->Prop)(detached:Values.val->Memory.mem->World->Prop)
  (io:Event->option gateway_native_io)(stable:World->block->Z->Prop)(thread_errno:World->int)
  (heap_allocation:block->Z->Prop).
Let native:=fun world object=>gateway_native_private(python world)object.
Let discipline:=gateway_python_discipline python objects detached.
Context(runtime:gateway_thread_runtime backend io native stable discipline thread_errno)
  (allocations:gateway_outcome_allocation_runtime backend python objects types default_allocator instances leases owned io native stable)
  (roots:gateway_root_lease_runtime backend python objects decimal_float leases)
  (object_threads:gateway_object_thread_contract backend native stable discipline heap_allocation python objects leases).

Definition gateway_outcome_class_context environment class description class_ticket held memory world:Prop:=
  gateway_objects_ready(python world)(objects world)memory /\types world class=Some description /\default_allocator world class /\
  leases world class_ticket class /\gateway_held_values python objects decimal_float leases held world /\
  gateway_native_environment native world memory environment.

Lemma gateway_outcome_class_context_ambient environment class description class_ticket held:
  Int.and(gateway_type_flags description)(Int.repr 256)=Int.repr 256 ->
  gateway_ambient_closed backend(gateway_outcome_class_context environment class description class_ticket held).
Proof.
  intros IMMUTABLE before world after next[NORMAL[TYPE[ALLOCATOR[LEASE[HELD ENVIRONMENT]]]]]INTERFERENCE.
  destruct(gateway_thread_ambient _ _ _ _ _ _ runtime None before world after next NORMAL INTERFERENCE)
    as[READY[[NATIVE STABLE]FRAME]].
  pose proof(gateway_lease_rooted backend python objects decimal_float leases roots world class_ticket class LEASE)as ROOT.
  destruct(@gateway_outcome_class_ambient World Event backend python objects types default_allocator instances leases owned io
    native stable allocations before world after next class description NORMAL ROOT TYPE ALLOCATOR IMMUTABLE INTERFERENCE)
    as[NEXT_ROOT[NEXT_TYPE NEXT_ALLOCATOR]].
  pose proof(@gateway_object_thread_ambient World Event backend native stable discipline heap_allocation python objects leases
    object_threads None before world after next NORMAL INTERFERENCE)as EFFECT.
  split;[exact READY|]. split;[exact NEXT_TYPE|]. split;[exact NEXT_ALLOCATOR|]. split;[apply(proj1 EFFECT);exact LEASE|].
  split;[eapply gateway_held_values_effect;[exact roots|exact HELD|exact EFFECT]|].
  intros identifier object ty LOOK;destruct(ENVIRONMENT identifier object ty LOOK)as[LIVE PRIVATE];split;
    [eapply Mem.valid_block_unchanged_on;[exact FRAME|exact LIVE]|apply NATIVE;assumption].
Qed.

Theorem gateway_actual_outcome_allocation environment parameters class description class_ticket held data_block data_offset
    before world events value after next descriptor:
  gateway_direct_io_projection backend io ->
  gateway_outcome_member_layout ge ->parameters!_copy=Some(Vptr data_block data_offset) ->
  gateway_type_basicsize description=24 ->gateway_type_itemsize description=0 ->
  Int.and(gateway_type_flags description)(Int.repr 256)=Int.repr 256 ->
  gateway_outcome_class_context environment class description class_ticket held before world ->
  gateway_steps backend ge
    (gateway_live(Callstate(External(EF_external "PyType_GenericAlloc"(mksignature[Xptr;Xlong]Xptr cc_default))
      [tptr(Tstruct __typeobject noattr);tlong](tptr(Tstruct __object noattr))cc_default)
      [class;Vlong Int64.zero](gateway_outcome_allocation_cont environment parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value<>Vnullptr ->
  exists object ticket,value=Vptr object Ptrofs.zero /\
    gateway_outcome_return_context python objects instances leases owned decimal_float
      object(Vptr data_block data_offset)class ticket held after next /\
    gateway_received_bytes io descriptor events=[].
Proof.
  intros PROJECTION LAYOUT COPY SIZE ITEMS IMMUTABLE INPUT RUN NONNULL.
  set(definition:=(External(EF_external "PyType_GenericAlloc"(mksignature[Xptr;Xlong]Xptr cc_default))
    [tptr(Tstruct __typeobject noattr);tlong](tptr(Tstruct __object noattr))cc_default:Ctypes.fundef Clight.function)).
  destruct(gateway_return_cut backend ge definition[class;Vlong Int64.zero](gateway_outcome_allocation_cont environment parameters)
    before world events(Returnstate value Kstop after)next ltac:(cbn;exact I)ltac:(cbn;lia)RUN)
    as(allocating &rest &allocated &allocator_after &allocator_next &EVENTS &ALLOCATION_RUN &REST).
  assert(ALLOCATED_NONNULL:allocated<>Vnullptr).
  { intro NULL;subst allocated;apply NONNULL;eapply gateway_actual_outcome_allocation_failure;exact REST. }
  destruct(gateway_external_operation_of_run backend ge _ _ _ _ _ _ _ _ _ _ _ ALLOCATION_RUN)
    as(pending &returned &called &called_world &changed &changed_world &observed &ALLOC_EVENTS &PENDING &PREFIX &OPERATION &SUFFIX).
  pose proof(gateway_outcome_class_context_ambient environment class description class_ticket held IMMUTABLE)as CLOSED.
  pose proof(gateway_pending_run_ready backend ge _ CLOSED(Callstate definition[class;Vlong Int64.zero]Kstop before)
    before world pending called called_world INPUT PENDING PREFIX)as CALLED.
  destruct CALLED as[NORMAL[TYPE[ALLOCATOR[CLASS_LEASE[HELD ENVIRONMENT]]]]].
  pose proof(gateway_lease_rooted backend python objects decimal_float leases roots called_world class_ticket class CLASS_LEASE)as ROOT.
  assert(API:gateway_object_operation backend gateway_api_generic_alloc[class;Vlong Int64.zero]
    called called_world allocated changed changed_world observed).
  { eexists;split;[exact actual_gateway_generic_alloc_abi|exact OPERATION]. }
  destruct(@gateway_outcome_generic_alloc World Event backend python objects types default_allocator instances leases owned io native stable
    allocations called called_world class description allocated changed changed_world observed NORMAL ROOT TYPE ALLOCATOR SIZE ITEMS IMMUTABLE API)
    as[ACCESS[FRAME[NONIO[NULL|NEW]]]];[contradiction|].
  destruct NEW as(object &ticket &ALLOCATED &FRESH &READY &CLASS &AFTER_TYPE &AFTER_ALLOCATOR &VALUE &PRIVATE &CREATED &CELL &ZERO
    &VALUES &PRIVACY);subst allocated.
  assert(EFFECT:gateway_object_thread_effect python objects leases called_world changed_world).
  { exact(conj(proj2(proj2 CREATED))(conj VALUES PRIVACY)). }
  assert(AFTER_HELD:gateway_held_values python objects decimal_float leases held changed_world).
  { eapply gateway_held_values_effect;[exact roots|exact HELD|exact EFFECT]. }
  assert(AFTER_ENVIRONMENT:gateway_native_environment native changed_world changed environment).
  { intros identifier candidate ty LOOK;destruct(ENVIRONMENT identifier candidate ty LOOK)as[LIVE NATIVE].
    split;[eapply Mem.valid_block_unchanged_on;[exact FRAME|exact LIVE]|apply(proj1 ACCESS);assumption]. }
  set(context:=gateway_outcome_construction_context python objects instances leases owned decimal_float
    environment object Vnullptr class ticket held).
  assert(AFTER_CONTEXT:context changed changed_world).
  { split;[exact(conj READY(conj CELL(conj ZERO(conj CLASS(conj(proj1 CREATED)AFTER_HELD)))))|exact AFTER_ENVIRONMENT]. }
  assert(CONTEXT_CLOSED:gateway_ambient_closed backend context).
  { eapply gateway_outcome_construction_ambient;[exact runtime|exact allocations|exact roots|exact object_threads]. }
  pose proof(gateway_readonly_run_side backend ge context CONTEXT_CLOSED(Returnstate(Vptr object Ptrofs.zero)Kstop changed)
    changed_world returned(Vptr object Ptrofs.zero)allocator_after allocator_next I AFTER_CONTEXT SUFFIX)as CALLER_READY.
  destruct(gateway_actual_constructed_outcome backend ge python objects types default_allocator instances leases owned decimal_float detached
    io stable thread_errno heap_allocation runtime allocations roots object_threads environment parameters object data_block data_offset class ticket held
    allocator_after allocator_next rest value after next LAYOUT COPY CALLER_READY REST)as[SAME[FINAL QUIET]].
  exists object,ticket;split;[exact SAME|]. split;[exact FINAL|].
  rewrite EVENTS,gateway_received_append.
  rewrite(gateway_object_run_no_direct_receive backend ge io gateway_api_generic_alloc definition[class;Vlong Int64.zero]
    before world allocating(Vptr object Ptrofs.zero)allocator_after allocator_next descriptor PROJECTION actual_gateway_generic_alloc_abi ALLOCATION_RUN).
  rewrite(gateway_quiet_received io descriptor rest QUIET);reflexivity.
Qed.

End OutcomeFactory.
