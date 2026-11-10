(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The same actual parser execution retains caller Cur/Max authority at return
   and its source-owned graph with the aggregate retained/retired reference budget. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine CallContexts.
From HostGateway Require Import GatewaySource GatewayImport GatewayContainerEncoding GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayObjectDiscipline
  GatewayObjectConstants GatewayObjectThreads GatewayObjectInstances GatewayContainerABI GatewayValueEntry GatewayValueContext
  GatewayReferenceLedger GatewayReferenceHeld GatewayReferenceValueProperties GatewayReferenceAccounting GatewayReferenceThreads GatewayReferenceNormalForm GatewayReferenceDecoded GatewayReferenceStackBound
  GatewayReferenceParserInputs GatewayReferenceParseResult GatewayReferenceParser GatewayReferenceAccountingStack GatewayReferenceReservations GatewayReferenceParserPool GatewayPermissionScopes GatewayPermissionEffects GatewayPermissionRuntime GatewayNativeMemory GatewayNoMemory GatewayObjectEvents
  GatewayScalarDecoding GatewayPathEvents GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.
Local Close Scope lean_scope.

Section ActualParserComplete.
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

Theorem gateway_reference_actual_parser_complete context ledger held reserved arguments
    stream_block stream_offset initial readonly original before world events value after next:
  is_call_cont context->gateway_reference_ledger_well_formed ledger->gateway_reference_stack_bound context ledger->
  gateway_reference_held python objects decimal_float ledger held world->gateway_reference_graphs_only held->
  (forall pointer,(count_occ Val.eq reserved pointer+gateway_reference_count ledger pointer<=python_native_strong(python world)pointer)%nat)->
  gateway_unicode_strict_mode original(Vptr mode_symbol Ptrofs.zero)->
  (forall object position,gateway_scalar_mode_region mode_symbol object position->readonly object position)->
  gateway_value_stream arguments=Vptr stream_block stream_offset->
  gateway_value_context native stable base stream_block stream_offset initial readonly original before world->
  (forall object position,readonly object position->native world object)->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_value)(gateway_value_arguments_list arguments)Kstop before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  gateway_reference_reserved_parse_result python objects decimal_float detached io stable(Clight.globalenv prog)context ledger held reserved
    stream_block stream_offset initial readonly original events value after next /\
  gateway_permission_frame(gateway_permission_region stream_block stream_offset readonly)before after.
Proof.
  intros CALL FORMED STACK HELD GRAPHS BUDGET MODE MODE_REGION STREAM INPUT READONLY RUN NONNULL.
  assert(RESULT:gateway_reference_reserved_parse_result python objects decimal_float detached io stable(Clight.globalenv prog)context ledger held reserved
    stream_block stream_offset initial readonly original events value after next).
  { eapply gateway_reference_actual_parser_with_reservations;eassumption. }
  split;[exact RESULT|].
  destruct RESULT as(final &final_stream &wire &ticket &DECODED &FINAL_CONTEXT &FINAL_NATIVE &DESCRIPTOR &FRAME &FINAL_BUDGET).
  destruct FINAL_CONTEXT as[SIDE[NATIVE[STABLE[INPUTS RETAINED]]]].
  eapply gateway_actual_return_permissions with(source:=Callstate(Internal f_host_value)(gateway_value_arguments_list arguments)Kstop before);
    [exact lifetimes|exact RUN|].
  intros object position[STREAM_CELL|READ].
  - destruct STREAM_CELL as[SAME RANGE];subst object;exists Cur,Writable.
    apply(gateway_value_stream_owned _ _ _ _ _ INPUTS position);exact RANGE.
  - exists Cur,Readable;apply(gateway_value_readonly_readable _ _ _ _ _ INPUTS object position);exact READ.
Qed.
End ActualParserComplete.
