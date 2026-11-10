(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Whole integer calls connect exact received tag/size/payload bytes
   to canonical decimal construction and the same actual source-owned return. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine CallContexts.
From HostGateway Require Import GatewaySource GatewayImport GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayObjectDiscipline
  GatewayObjectThreads GatewayValue GatewayValueEntry GatewayValueContext GatewayValueStack GatewayValueActual
  GatewayValueNodeMemory GatewayValueTag GatewayScalarLength GatewayScalarContext GatewayScalarSize GatewayScalarBuffer GatewayScalarPayload
  GatewayScalarPayloadMemory GatewayScalarSizedFrames GatewayReferenceInteger GatewayValueStreamRelations GatewayScalarAllocationPath GatewayScalarReadPath GatewayScalarReadMemory
  GatewayNativeRegions GatewayRegionThreads GatewayRegionMemory GatewayNativeMemory GatewayNoMemory GatewayObjectEvents
  GatewayScalarEncoding GatewayWordValues GatewayPathEvents GatewayStreamInterface GatewayThreadRuntime
  GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceActivation GatewayReferenceAccounting GatewayReferenceThreads GatewayThreadInvariant
  GatewayReferenceNormalForm GatewayReferenceStackBound GatewayReferenceOwnedInteger GatewayReferenceDecoded GatewayReferenceParseResult GatewayContainerEncoding GatewayReferenceValueProperties.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Theorem gateway_reference_parse_integer {World Event}(backend:gateway_backend World Event)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (allocations:gateway_native_memory_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)heap_allocation)
    (constructors:gateway_objects_runtime backend python objects decimal_float)
    (reference_threads:gateway_reference_thread_contract backend(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (errors:gateway_no_memory_runtime backend python)(io_projection:gateway_direct_io_projection backend io)
    context ledger held arguments before world events value after next stream_block stream_offset initial readonly original byte remaining :
  is_call_cont context->gateway_reference_ledger_well_formed ledger->gateway_reference_stack_bound context ledger->
  gateway_reference_source_bound(Clight.globalenv prog)
    (Callstate(Internal f_host_value)(gateway_value_arguments_list arguments)context before)ledger->
  gateway_reference_scope python objects decimal_float ledger held world->
  Byte.unsigned byte=3 ->gateway_value_stream arguments=Vptr stream_block stream_offset ->
  gateway_value_context(fun current candidate=>gateway_native_private(python current)candidate)stable
    (gateway_python_discipline python objects detached)stream_block stream_offset initial readonly original before world ->
  (forall candidate position,readonly candidate position ->gateway_native_private(python world)candidate) ->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_value)(gateway_value_arguments_list arguments)Kstop before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value<>Vnullptr ->
  gateway_received_bytes io(stream_descriptor initial)events=byte::remaining ->
  gateway_reference_parse_result python objects decimal_float detached io stable(Clight.globalenv prog)context ledger held
    stream_block stream_offset initial readonly original events value after next.
Proof.
  intros CALL FORMED OLDER BOUND SCOPE TAG STREAM INPUT READONLY RUN NONNULL OBSERVED.
  destruct(gateway_reference_actual_integer_stream_value_owned backend python objects decimal_float detached io stable thread_errno heap_allocation
    runtime allocations constructors reference_threads errors io_projection context ledger held arguments before world events value after next stream_block stream_offset initial readonly original byte remaining CALL FORMED OLDER BOUND SCOPE TAG STREAM INPUT READONLY RUN NONNULL OBSERVED)
    as(final &final_stream &WELL &OWNER &BINDING &[FINAL_CONTEXT FINAL_NATIVE] &size_bytes &payload &integer &
      WIDTH &COUNT &BYTES &STREAM_AFTER &DECODED &HELD &VALUE &ENTRIES &FINAL_BOUND).
  exists final,final_stream,(gateway_wire_scalar 3 payload),(gateway_reference_next ledger).
  split.
  - eapply gateway_reference_leaf_receipt with(captured:={|gateway_held_ticket:=gateway_reference_next ledger;
      gateway_held_object:=value;gateway_held_view:=gateway_held_scalar_value(gateway_long_object integer)|});
      [exact WELL|exact ENTRIES|apply Nat.le_refl|exact FINAL_BOUND|exact OWNER|exact HELD|reflexivity|reflexivity|exact VALUE|constructor].
  - split;[exact FINAL_CONTEXT|]. split;[exact FINAL_NATIVE|]. split;
      [eapply gateway_scalar_stream_descriptor;exact STREAM_AFTER|]. constructor;rewrite BYTES.
    exact(gateway_scalar_source_encoding gateway_scalar_long byte size_bytes payload TAG WIDTH COUNT).
Qed.
