(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual parser returns its real source-owned graph together with one
   conserved budget for caller, retained-global and retired reference occurrences. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine CallContexts.
From HostGateway Require Import GatewaySource GatewayImport GatewayContainerEncoding GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayObjectDiscipline
  GatewayObjectConstants GatewayObjectThreads GatewayObjectInstances GatewayContainerABI GatewayValueEntry GatewayValueContext
  GatewayReferenceLedger GatewayReferenceHeld GatewayReferenceValueProperties GatewayReferenceAccounting GatewayReferenceThreads GatewayReferenceNormalForm GatewayReferenceDecoded GatewayReferenceStackBound
  GatewayReferenceParserInputs GatewayReferenceParseResult GatewayReferenceParser GatewayReferenceAccountingStack GatewayReferenceReservations GatewayNativeMemory GatewayNoMemory GatewayObjectEvents
  GatewayScalarDecoding GatewayPathEvents GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.
Local Close Scope lean_scope.

Section ActualParserPool.
Context {World Event}(backend:gateway_backend World Event)
  (python:World->python_world)(objects:World->gateway_object_heap)(decimal_float:list Z->Floats.float->Prop)
  (detached:Values.val->Memory.mem->World->Prop)(io:Event->option gateway_native_io)
  (stable:World->block->Z->Prop)(thread_errno:World->int)(heap_allocation:block->Z->Prop).
Let native:=fun current object=>gateway_native_private(python current)object.
Let base:=gateway_python_discipline python objects detached.
Context(runtime:gateway_thread_runtime backend io native stable base thread_errno)
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

Theorem gateway_reference_actual_parser_with_reservations context ledger held reserved arguments
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
    stream_block stream_offset initial readonly original events value after next.
Proof.
  intros CALL FORMED STACK HELD GRAPHS BUDGET MODE MODE_REGION STREAM INPUT READONLY RUN NONNULL.
  assert(SCOPE:gateway_reference_scope python objects decimal_float ledger held world).
  { split;[|exact HELD]. intro pointer;pose proof(BUDGET pointer);lia. }
  apply gateway_reference_received_result_reservations.
  - eapply gateway_reference_actual_parser;eassumption.
  - eapply gateway_reference_actual_parser_reservations;eassumption.
Qed.
End ActualParserPool.
