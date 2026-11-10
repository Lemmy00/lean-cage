(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Whole null calls consume their actual byte and retain the inline return reference. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine CallContexts.
From HostGateway Require Import GatewaySource GatewayImport GatewayMachine GatewayContexts GatewayPython GatewayObjects
  GatewayReferences GatewayValue GatewayObjectDiscipline GatewayObjectConstants GatewayObjectThreads GatewayPrimitiveBindings
  GatewayPrimitiveValues GatewayPrimitiveMemory GatewayPrimitiveEncoding GatewayValueEntry GatewayValueContext GatewayValueStack
  GatewayValueActual GatewayValueRegions GatewayValueNodeMemory GatewayValueReturnContext GatewayValueBoolean GatewayNativeRegions GatewayRegionThreads
  GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting GatewayReferenceHeld GatewayReferenceThreads
  GatewayReferenceActivation GatewayReferenceNull GatewayThreadInvariant GatewayStreamInterface GatewayThreadRuntime
  GatewayObjectEvents GatewayPathEvents.
Import ListNotations.
Local Close Scope lean_scope.

Section NullValue.
Context {World Event}(backend:gateway_backend World Event)
  (python:World->python_world)(objects:World->gateway_object_heap)
  (detached:Values.val->Memory.mem->World->Prop)(io:Event->option gateway_native_io)
  (stable:World->block->Z->Prop)(thread_errno:World->int)(heap_allocation:block->Z->Prop)
  (decimal_float:list Z->Floats.float->Prop).
Let native:=fun world object=>gateway_native_private(python world)object.
Let base:=gateway_python_discipline python objects detached.
Context(runtime:gateway_thread_runtime backend io native stable base thread_errno)
  (constructors:gateway_objects_runtime backend python objects decimal_float)
  (references:gateway_reference_runtime backend python objects)
  (reference_threads:gateway_reference_thread_contract backend native stable base heap_allocation python objects)
  (projection:gateway_direct_io_projection backend io).

Theorem gateway_reference_actual_null_value context ledger held byte remaining arguments before world events value after next
    stream_block stream_offset initial readonly original none_symbol:
  is_call_cont context->gateway_reference_ledger_well_formed ledger->
  gateway_reference_source_bound(Clight.globalenv prog)
    (Callstate(Internal f_host_value)(gateway_value_arguments_list arguments)context before)ledger->
  gateway_reference_scope python objects decimal_float ledger held world->
  gateway_none_runtime python objects(Vptr none_symbol Ptrofs.zero)->
  Genv.find_symbol(Clight.globalenv prog)__Py_NoneStruct=Some none_symbol->
  Byte.unsigned byte=0->
  gateway_value_stream arguments=Vptr stream_block stream_offset->
  gateway_value_context native stable base stream_block stream_offset initial readonly original before world->
  (forall object position,readonly object position->native world object)->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_value)(gateway_value_arguments_list arguments)Kstop before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  gateway_received_bytes io(stream_descriptor initial)events=byte::remaining->
  exists final final_stream,
    gateway_stream_read_after(gateway_stream_node_debit initial)1 final_stream /\
    gateway_value_context native stable base stream_block stream_offset final_stream readonly original after next /\
    (forall object position,readonly object position->native next object) /\
    gateway_reference_ledger_well_formed final /\
    gateway_reference_owns final(gateway_reference_result(gateway_reference_depth context))
      (gateway_reference_next ledger)value /\
    gateway_reference_place_value(Clight.globalenv prog)(Returnstate value context after)
      (gateway_reference_result(gateway_reference_depth context))value /\
    gateway_reference_scope python objects decimal_float final
      (held++[{|gateway_held_ticket:=gateway_reference_next ledger;gateway_held_object:=value;
        gateway_held_view:=gateway_held_scalar_value(gateway_none_object)|}])next /\
    gateway_value_heap decimal_float(objects next)value
      LeanCage_Host_GatewayResponseCode_Value_null /\
    gateway_received_bytes io(stream_descriptor initial)events=[byte].
Proof.
  intros CALL FORMED BOUND SCOPE CONSTANTS NONE TAG STREAM INPUT READONLY RUN NONNULL OBSERVED.
  destruct(gateway_reference_fresh_call_places(Clight.globalenv prog)(Internal f_host_value)
    (gateway_value_arguments_list arguments)context before ledger BOUND)as[TEMPS RESULTS].
  set(scoped:=gateway_thread_invariant_discipline base(gateway_reference_scope python objects decimal_float ledger held)).
  pose proof(gateway_thread_with_reference_scope backend io native stable base thread_errno heap_allocation
    python objects decimal_float reference_threads ledger held runtime)as SCOPE_RUNTIME.
  set(augmented:=gateway_native_region_discipline native scoped readonly).
  pose proof(gateway_thread_with_native_region backend io native stable scoped thread_errno SCOPE_RUNTIME readonly)as THREADS.
  assert(AUGMENTED_INPUT:gateway_value_context native stable augmented stream_block stream_offset initial readonly original before world).
  { pose proof INPUT as[SIDE CONTEXT];split.
    - split;[split;[exact SIDE|exact SCOPE]|].
      assert(ALL:gateway_native_region_owned native(gateway_value_input_region stream_block stream_offset readonly)before world)
        by(eapply gateway_value_return_native_region;[exact INPUT|exact READONLY]).
      intros object position POINT;exact(ALL object position(or_intror POINT)).
    - exact CONTEXT. }
  destruct(gateway_actual_value_tag backend io native stable augmented thread_errno THREADS arguments before world events value after next
    stream_block stream_offset initial readonly original STREAM AUGMENTED_INPUT RUN NONNULL)
    as(slots &selected &prefix &reading &suffix &word_before &word_world &word_after &word_next &final_stream &
      EVENTS &DEPTH &NODES &QUIET &PREFIX &ALLOCATED &READ &READ_BYTES &LOAD &STREAM_AFTER &ACTIVE &SUFFIX).
  assert(SELECTED:selected=byte).
  { rewrite EVENTS,!gateway_received_append,(gateway_quiet_received io(stream_descriptor initial)prefix QUIET),READ_BYTES
      in OBSERVED;inversion OBSERVED;reflexivity. }
  subst selected.
  rewrite TAG in LOAD.
  pose proof ACTIVE as[[[[SIDE SCOPE_AT_TAG]OWNED_READONLY]CONTEXT]STACK].
  assert(SCOPED_ACTIVE:gateway_value_active native stable scoped slots stream_block stream_offset final_stream readonly original
    word_after word_next).
  { split;[split;[split;[exact SIDE|exact SCOPE_AT_TAG]|exact CONTEXT]|exact STACK]. }
  destruct actual_gateway_incref_binding as[reference_symbol[REFERENCE FUNCTION]].
  destruct(gateway_reference_actual_null_branch backend(Clight.globalenv prog)python objects detached io stable thread_errno
    heap_allocation decimal_float runtime references reference_threads projection context ledger held slots arguments initial
    stream_block stream_offset final_stream readonly original word_after word_next suffix value after next none_symbol reference_symbol
    (stream_descriptor initial)CALL FORMED(RESULTS(gateway_reference_depth context))CONSTANTS NONE REFERENCE FUNCTION
    (conj SCOPED_ACTIVE LOAD)SUFFIX)
    as(final &RETURNED &WELL &OWNED &BINDING &HELD &VALUE &FINAL_SIDE &EMPTY &ORIGIN).
  assert(BASE_ACTIVE:gateway_value_active native stable base slots stream_block stream_offset final_stream readonly original word_after word_next).
  { split;[split;[exact SIDE|exact CONTEXT]|exact STACK]. }
  set(protected:=gateway_value_input_region stream_block stream_offset readonly).
  assert(OWNED_INPUT:gateway_native_region_owned native protected word_after word_next).
  { eapply gateway_value_return_native_region;[exact(proj1 BASE_ACTIVE)|].
    intros object position POINT;exact(proj2(OWNED_READONLY object position POINT)). }
  assert(MEMORY_INPUT:gateway_value_tagged native stable base slots stream_block stream_offset final_stream readonly original
    (Int64.repr(gateway_primitive_tag gateway_primitive_null))word_after word_next).
  { split;[exact BASE_ACTIVE|exact LOAD]. }
  pose proof(gateway_actual_primitive_branch_memory backend python objects detached io stable thread_errno decimal_float runtime
    constructors references gateway_primitive_null slots arguments initial stream_block stream_offset final_stream readonly original
    protected word_after word_next suffix value after next none_symbol CONSTANTS NONE MEMORY_INPUT OWNED_INPUT
    (gateway_value_environment_avoids_inputs native stable base slots stream_block stream_offset final_stream readonly original
      word_after word_next BASE_ACTIVE)SUFFIX NONNULL)as[MEMORY_SIDE[FINAL_OWNED FRAME]].
  assert(BYTES:gateway_received_bytes io(stream_descriptor initial)events=[byte]).
  { rewrite EVENTS,!gateway_received_append,(gateway_quiet_received io(stream_descriptor initial)prefix QUIET),READ_BYTES,EMPTY;
      reflexivity. }
  exists final,final_stream;split;[exact STREAM_AFTER|]. split.
  - eapply gateway_value_context_return_frame;[exact runtime|exact(proj1 BASE_ACTIVE)|exact FINAL_SIDE|exact FINAL_OWNED|exact FRAME].
  - split;[intros object position POINT;exact(proj2(FINAL_OWNED object position(or_intror POINT)))|].
    split;[exact WELL|]. split;[exact OWNED|]. split;[exact BINDING|]. split;[exact HELD|].
    split;[exact VALUE|exact BYTES].
Qed.

Theorem gateway_reference_actual_null_framing context ledger held byte remaining arguments before world events value after next
    stream_block stream_offset initial readonly original none_symbol:
  is_call_cont context->gateway_reference_ledger_well_formed ledger->
  gateway_reference_source_bound(Clight.globalenv prog)
    (Callstate(Internal f_host_value)(gateway_value_arguments_list arguments)context before)ledger->
  gateway_reference_scope python objects decimal_float ledger held world->
  gateway_none_runtime python objects(Vptr none_symbol Ptrofs.zero)->
  Genv.find_symbol(Clight.globalenv prog)__Py_NoneStruct=Some none_symbol->
  Byte.unsigned byte=0->
  gateway_value_stream arguments=Vptr stream_block stream_offset->
  gateway_value_context native stable base stream_block stream_offset initial readonly original before world->
  (forall object position,readonly object position->native world object)->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_value)(gateway_value_arguments_list arguments)Kstop before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  gateway_received_bytes io(stream_descriptor initial)events=byte::remaining->
  LeanCage_Host_GatewayResponseWords_SourceEncoded
    (LeanCage_Host_GatewayResponseCode_Subject_value
      LeanCage_Host_GatewayResponseCode_Value_null)
    (gateway_wire_bytes(gateway_received_bytes io(stream_descriptor initial)events)).
Proof.
  intros CALL FORMED BOUND SCOPE CONSTANTS NONE TAG STREAM INPUT READONLY RUN NONNULL OBSERVED.
  destruct(gateway_reference_actual_null_value context ledger held byte remaining arguments before world events value after next
    stream_block stream_offset initial readonly original none_symbol CALL FORMED BOUND SCOPE CONSTANTS NONE TAG STREAM INPUT READONLY
    RUN NONNULL OBSERVED)as(final &final_stream &READ &CONTEXT &NATIVE &WELL &OWNED &BINDING &HELD &VALUE &BYTES).
  rewrite BYTES;apply gateway_null_source_encoding;exact TAG.
Qed.

End NullValue.
