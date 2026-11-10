(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Whole native decoder calls derive primitive values from their actual input byte. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayImport GatewayMachine GatewayPython GatewayObjects GatewayReferences
  GatewayRootLeases GatewayObjectDiscipline GatewayObjectThreads GatewayValue GatewayObjectConstants
  GatewayValueEntry GatewayValueContext GatewayValueActual GatewayValueRegions GatewayValueNullHeap GatewayValueBooleanHeap
  GatewayValueBoolean GatewayValueNodeMemory GatewayPrimitiveBindings GatewayPrimitiveEncoding GatewayBindings
  GatewayObjectEvents GatewayPathEvents GatewayStreamInterface GatewayThreadRuntime GatewayFramedRuntime.
Import ListNotations.
Local Close Scope lean_scope.

Inductive gateway_primitive_case:=gateway_primitive_null|gateway_primitive_boolean(flag:bool).
Definition gateway_primitive_tag primitive :Z:=
  match primitive with gateway_primitive_null=>0|gateway_primitive_boolean flag=>if flag then 2 else 1 end.
Definition gateway_primitive_object primitive:=
  match primitive with gateway_primitive_null=>gateway_none_object|gateway_primitive_boolean flag=>gateway_bool_object flag end.
Definition gateway_primitive_wire primitive:=
  match primitive with
  |gateway_primitive_null=>LeanCage_Host_GatewayResponseCode_Value_null
  |gateway_primitive_boolean flag=>LeanCage_Host_GatewayResponseCode_Value_boolean(if flag then Bool_true else Bool_false)
  end.

Section PrimitiveValues.
Context {World Event}(backend:gateway_backend World Event)
  (python:World->python_world)(objects:World->gateway_object_heap)
  (detached:Values.val->Memory.mem->World->Prop)(io:Event->option gateway_native_io)
  (stable:World->block->Z->Prop)(thread_errno:World->int)(heap_allocation:block->BinNums.Z->Prop)
  (decimal_float:list BinNums.Z->Floats.float->Prop)(leases:World->nat->Values.val->Prop).
Let native:=fun world object=>gateway_native_private(python world)object.
Let base:=gateway_python_discipline python objects detached.
Context(runtime:gateway_thread_runtime backend io native stable base thread_errno)
  (constructors:gateway_objects_runtime backend python objects decimal_float)
  (references:gateway_reference_runtime backend python objects)
  (roots:gateway_root_lease_runtime backend python objects decimal_float leases)
  (object_threads:gateway_object_thread_contract backend native stable base heap_allocation python objects leases)
  (projection:gateway_direct_io_projection backend io).

Theorem gateway_actual_primitive_value primitive byte remaining arguments before world events value after next
    stream_block stream_offset initial readonly original none_symbol :
  gateway_none_runtime python objects(Vptr none_symbol Ptrofs.zero) ->
  Genv.find_symbol(Clight.globalenv prog)__Py_NoneStruct=Some none_symbol ->
  Byte.unsigned byte=gateway_primitive_tag primitive ->
  gateway_value_stream arguments=Vptr stream_block stream_offset ->
  gateway_value_context native stable base stream_block stream_offset initial readonly original before world ->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_value)(gateway_value_arguments_list arguments)Kstop before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value<>Vnullptr ->
  gateway_received_bytes io(stream_descriptor initial)events=byte::remaining ->
  exists ticket,gateway_held_values python objects decimal_float leases
      [{|gateway_held_ticket:=ticket;gateway_held_object:=value;
        gateway_held_view:=gateway_held_scalar_value(gateway_primitive_object primitive)|}]next /\
    gateway_value_heap decimal_float(objects next)value(gateway_primitive_wire primitive) /\
    base None after next /\gateway_received_bytes io(stream_descriptor initial)events=[byte].
Proof.
  intros CONSTANTS NONE TAG STREAM INPUT RUN NONNULL OBSERVED.
  destruct(gateway_actual_value_tag backend io native stable base thread_errno runtime
    arguments before world events value after next stream_block stream_offset initial readonly original STREAM INPUT RUN NONNULL)
    as(slots &selected &prefix &reading &suffix &word_before &word_world &word_after &word_next &final_stream &
      EVENTS &DEPTH &NODES &QUIET &PREFIX &ALLOCATED &READ &READ_BYTES &LOAD &STREAM_AFTER &ACTIVE &SUFFIX).
  assert(SELECTED:selected=byte).
  { rewrite EVENTS,!gateway_received_append,(gateway_quiet_received io(stream_descriptor initial)prefix QUIET),READ_BYTES
      in OBSERVED;inversion OBSERVED;reflexivity. }
  subst selected;rewrite TAG in LOAD.
  assert(BRANCH:exists ticket,gateway_held_values python objects decimal_float leases
      [{|gateway_held_ticket:=ticket;gateway_held_object:=value;
        gateway_held_view:=gateway_held_scalar_value(gateway_primitive_object primitive)|}]next /\
    gateway_value_heap decimal_float(objects next)value(gateway_primitive_wire primitive) /\
    base None after next /\gateway_received_bytes io(stream_descriptor initial)suffix=[]).
  { destruct primitive as[|flag].
    - destruct actual_gateway_incref_binding as[reference_symbol[REFERENCE FUNCTION]].
      destruct(gateway_actual_null_branch backend(Clight.globalenv prog)python objects detached io stable thread_errno
        heap_allocation decimal_float leases runtime references roots object_threads projection
        slots arguments initial stream_block stream_offset final_stream readonly original word_after word_next suffix value after next
        none_symbol reference_symbol(stream_descriptor initial)CONSTANTS NONE REFERENCE FUNCTION(conj ACTIVE LOAD)SUFFIX)
        as(ticket &VALUE &HELD &HEAP &SIDE &EMPTY).
      exists ticket;split;[exact HELD|]. split;[exact HEAP|]. split;assumption.
    - destruct actual_gateway_boolean_binding as[definition[DEFINITION[[symbol[SYMBOL FUNCTION]]TYPE]]].
      eapply(gateway_actual_boolean_branch backend(Clight.globalenv prog)python objects detached io stable thread_errno
        heap_allocation decimal_float leases runtime constructors roots object_threads projection
        flag slots arguments initial stream_block stream_offset final_stream readonly original word_after word_next suffix value after next
        symbol definition(stream_descriptor initial)DEFINITION SYMBOL FUNCTION TYPE);[|exact SUFFIX|exact NONNULL].
      split;[exact ACTIVE|];destruct flag;exact LOAD. }
  destruct BRANCH as(ticket &HELD &HEAP &SIDE &EMPTY).
  assert(BYTES:gateway_received_bytes io(stream_descriptor initial)events=[byte]).
  { rewrite EVENTS,!gateway_received_append,(gateway_quiet_received io(stream_descriptor initial)prefix QUIET),READ_BYTES,EMPTY;
      reflexivity. }
  exists ticket;split;[exact HELD|]. split;[exact HEAP|]. split;assumption.
Qed.

Theorem gateway_actual_primitive_framing primitive byte remaining arguments before world events value after next
    stream_block stream_offset initial readonly original none_symbol :
  gateway_none_runtime python objects(Vptr none_symbol Ptrofs.zero) ->
  Genv.find_symbol(Clight.globalenv prog)__Py_NoneStruct=Some none_symbol ->
  Byte.unsigned byte=gateway_primitive_tag primitive ->
  gateway_value_stream arguments=Vptr stream_block stream_offset ->
  gateway_value_context native stable base stream_block stream_offset initial readonly original before world ->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_value)(gateway_value_arguments_list arguments)Kstop before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value<>Vnullptr ->
  gateway_received_bytes io(stream_descriptor initial)events=byte::remaining ->
  LeanCage_Host_GatewayResponseWords_SourceEncoded
    (LeanCage_Host_GatewayResponseCode_Subject_value(gateway_primitive_wire primitive))
    (gateway_wire_bytes(gateway_received_bytes io(stream_descriptor initial)events)).
Proof.
  intros CONSTANTS NONE TAG STREAM INPUT RUN NONNULL OBSERVED.
  destruct(gateway_actual_primitive_value primitive byte remaining arguments before world events value after next
    stream_block stream_offset initial readonly original none_symbol CONSTANTS NONE TAG STREAM INPUT RUN NONNULL OBSERVED)
    as(ticket &HELD &HEAP &SIDE &BYTES).
  rewrite BYTES;destruct primitive as[|flag].
  - apply gateway_null_source_encoding;exact TAG.
  - apply gateway_boolean_source_encoding;exact TAG.
Qed.

End PrimitiveValues.
