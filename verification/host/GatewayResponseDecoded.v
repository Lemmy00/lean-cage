(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The real exchange invokes the checked recursive decoder on
   the same stream and preserves the actual returned graph through its caller cut. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine CallContexts.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayPython GatewayObjects GatewayReferences
  GatewayObjectDiscipline GatewayObjectConstants GatewayObjectThreads GatewayObjectInstances GatewayContainerABI
  GatewayValueEntry GatewayValueContext GatewayReferenceLedger GatewayReferenceHeld GatewayReferenceAccounting
  GatewayReferenceThreads GatewayReferenceStackBound GatewayReferenceValueProperties GatewayReferenceParseResult
  GatewayReferenceReservations GatewayReferenceParserComplete GatewayPermissionScopes GatewayPermissionEffects GatewayPermissionRuntime
  GatewayNativeMemory GatewayNoMemory GatewayObjectEvents
  GatewayScalarDecoding GatewayPathEvents GatewayStreamInterface GatewayThreadRuntime GatewayResponseParserSource GatewayParserReturn.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Section ActualResponseDecode.
Context {World Event}(backend:gateway_backend World Event)
  (python:World->python_world)(objects:World->gateway_object_heap)(decimal_float:list Z->Floats.float->Prop)
  (detached:Values.val->Memory.mem->World->Prop)(io:Event->option gateway_native_io)
  (stable:World->block->Z->Prop)(thread_errno:World->int)(heap_allocation:block->Z->Prop).
Let native:=fun current object=>gateway_native_private(python current)object.
Let base:=gateway_python_discipline python objects detached.
Context(runtime:gateway_thread_runtime backend io native stable base thread_errno)
  (lifetimes:gateway_allocation_lifetime_runtime backend)
  (allocations:gateway_native_memory_runtime backend io native stable base heap_allocation)
  (constructors:gateway_objects_runtime backend python objects decimal_float)
  (references:gateway_reference_runtime backend python objects)
  (reference_threads:gateway_reference_thread_contract backend native stable base heap_allocation python objects)
  (containers:gateway_container_runtime backend python objects)(abi:gateway_container_abi_runtime backend python objects)
  (instances:gateway_instance_runtime backend(Clight.globalenv prog)python objects(fun _ _ _=>Logic.False))
  (errors:gateway_no_memory_runtime backend python)(projection:gateway_direct_io_projection backend io)
  (none_symbol mode_symbol:block)
  (constants:gateway_none_runtime python objects(Vptr none_symbol Ptrofs.zero))
  (NONE:Genv.find_symbol(Clight.globalenv prog)__Py_NoneStruct=Some none_symbol)
  (MODE_SYMBOL:Genv.find_symbol(Clight.globalenv prog)___stringlit_8=Some mode_symbol).

Theorem actual_exchange_decodes_response environment temporaries ledger held reserved
    stream initial readonly original before world events value after next:
  gateway_reference_ledger_well_formed ledger->
  gateway_reference_stack_bound(response_parser_cont environment temporaries)ledger->
  gateway_reference_held python objects decimal_float ledger held world->gateway_reference_graphs_only held->
  (forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count ledger pointer<=
    python_native_strong(python world)pointer)%nat)->
  gateway_unicode_strict_mode original(Vptr mode_symbol Ptrofs.zero)->
  (forall object position,gateway_scalar_mode_region mode_symbol object position->readonly object position)->
  gateway_value_context native stable base stream Ptrofs.zero initial readonly original before world->
  (forall object position,readonly object position->native world object)->
  value<>Vnullptr->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_value)(response_parser_arguments stream)
      (response_parser_cont environment temporaries)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists body caller_events parsed memory current,
    events=body++caller_events /\parsed<>Vnullptr /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(Internal f_host_value)(response_parser_arguments stream)Kstop before)world)body
      (gateway_live(Returnstate parsed Kstop memory)current) /\
    gateway_reference_reserved_parse_result python objects decimal_float detached io stable(Clight.globalenv prog)
      (response_parser_cont environment temporaries)ledger held reserved stream Ptrofs.zero initial readonly original body parsed memory current /\
    gateway_reference_parse_result python objects decimal_float detached io stable(Clight.globalenv prog)
      (response_parser_cont environment temporaries)ledger held stream Ptrofs.zero initial readonly original body parsed memory current /\
    gateway_permission_frame(gateway_permission_region stream Ptrofs.zero readonly)before memory /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate parsed(response_parser_cont environment temporaries)memory)current)caller_events
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros FORMED STACK HELD GRAPHS BUDGET MODE MODE_REGION INPUT READONLY NONNULL RUN.
  destruct(gateway_return_cut backend(Clight.globalenv prog)(Internal f_host_value)(response_parser_arguments stream)
    (response_parser_cont environment temporaries)before world events(Returnstate value Kstop after)next I
    ltac:(cbn[gateway_continuation gateway_cont_weight response_parser_cont];lia)RUN)
    as(body&caller_events&parsed&memory&current&EVENTS&BODY&CALLER).
  assert(PARSED_NONNULL:parsed<>Vnullptr).
  { eapply actual_successful_parser_return;[exact NONNULL|exact CALLER]. }
  set(arguments:={|gateway_value_stream:=Vptr stream Ptrofs.zero;gateway_value_depth:=Int.repr 72|}).
  assert(COMPLETE:gateway_reference_reserved_parse_result python objects decimal_float detached io stable(Clight.globalenv prog)
    (response_parser_cont environment temporaries)ledger held reserved stream Ptrofs.zero initial readonly original body parsed memory current /\
    gateway_permission_frame(gateway_permission_region stream Ptrofs.zero readonly)before memory).
  { eapply gateway_reference_actual_parser_complete with(arguments:=arguments);
      try eassumption;[exact I|reflexivity]. }
  destruct COMPLETE as[DECODED PERMISSIONS].
  assert(COMMON:gateway_reference_parse_result python objects decimal_float detached io stable(Clight.globalenv prog)
    (response_parser_cont environment temporaries)ledger held stream Ptrofs.zero initial readonly original body parsed memory current).
  { destruct DECODED as(final&final_stream&wire&ticket&OWNER&CONTEXT&NATIVE&DESCRIPTOR&FRAME&RESERVED).
    exists final,final_stream,wire,ticket;split;[exact OWNER|]. split;[exact CONTEXT|].
    split;[exact NATIVE|]. split;[exact DESCRIPTOR|exact FRAME]. }
  exists body,caller_events,parsed,memory,current;split;[exact EVENTS|]. split;[exact PARSED_NONNULL|].
  split;[exact BODY|]. split;[exact DECODED|]. split;[exact COMMON|]. split;[exact PERMISSIONS|exact CALLER].
Qed.
End ActualResponseDecode.
