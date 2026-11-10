(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Whole primitive decoder calls retain the debited actual stream for their caller. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences
  GatewayObjectConstants GatewayObjectDiscipline GatewayPrimitiveValues GatewayPrimitiveMemory GatewayRegionThreads
  GatewayValueEntry GatewayValueContext GatewayValueStack GatewayValueActual GatewayValueRegions GatewayValueProjection
  GatewayValueNodeMemory GatewayNativeRegions GatewayStreamInterface GatewayThreadRuntime GatewayPathEvents.
Import ListNotations.

Section PrimitiveStream.
Context {World Event}(backend:gateway_backend World Event)
  (python:World->python_world)(objects:World->gateway_object_heap)
  (detached:Values.val->Memory.mem->World->Prop)(io:Event->option gateway_native_io)
  (stable:World->block->Z->Prop)(thread_errno:World->int)(decimal_float:list Z->Floats.float->Prop).
Let native:=fun world object=>gateway_native_private(python world)object.
Let base:=gateway_python_discipline python objects detached.
Context(runtime:gateway_thread_runtime backend io native stable base thread_errno)
  (constructors:gateway_objects_runtime backend python objects decimal_float)
  (references:gateway_reference_runtime backend python objects).

Theorem gateway_actual_primitive_stream primitive byte remaining arguments before world events value after next
    stream_block stream_offset initial readonly original none_symbol :
  gateway_none_runtime python objects(Vptr none_symbol Ptrofs.zero) ->
  Genv.find_symbol(Clight.globalenv prog)__Py_NoneStruct=Some none_symbol ->
  Byte.unsigned byte=gateway_primitive_tag primitive ->
  gateway_value_stream arguments=Vptr stream_block stream_offset ->
  gateway_value_context native stable base stream_block stream_offset initial readonly original before world ->
  (forall object position,readonly object position ->native world object) ->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_value)(gateway_value_arguments_list arguments)Kstop before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value<>Vnullptr ->
  gateway_received_bytes io(stream_descriptor initial)events=byte::remaining ->
  exists final_stream,gateway_stream_read_after(gateway_stream_node_debit initial)1 final_stream /\
    gateway_value_context native stable base stream_block stream_offset final_stream readonly original after next /\
    gateway_native_region_owned native(gateway_value_input_region stream_block stream_offset readonly)after next.
Proof.
  intros CONSTANTS NONE TAG STREAM INPUT READONLY RUN NONNULL OBSERVED.
  set(protected:=gateway_value_input_region stream_block stream_offset readonly).
  set(augmented:=gateway_native_region_discipline native base protected).
  pose proof(gateway_thread_with_native_region backend io native stable base thread_errno runtime protected)as AUGMENTED_RUNTIME.
  assert(OWNED:gateway_native_region_owned native protected before world).
  { eapply gateway_value_context_native_region;[exact INPUT|exact READONLY]. }
  assert(AUGMENTED_INPUT:gateway_value_context native stable augmented stream_block stream_offset initial readonly original before world).
  { destruct INPUT as[SIDE REST];split;[split;[exact SIDE|exact OWNED]|exact REST]. }
  destruct(gateway_actual_value_tag backend io native stable augmented thread_errno AUGMENTED_RUNTIME
    arguments before world events value after next stream_block stream_offset initial readonly original
    STREAM AUGMENTED_INPUT RUN NONNULL)
    as(slots &selected &prefix &reading &suffix &word_before &word_world &word_after &word_next &final_stream &
      EVENTS &DEPTH &NODES &QUIET &PREFIX &ALLOCATED &READ &READ_BYTES &LOAD &STREAM_AFTER &ACTIVE &SUFFIX).
  assert(SELECTED:selected=byte).
  { rewrite EVENTS,!gateway_received_append,(gateway_quiet_received io(stream_descriptor initial)prefix QUIET),READ_BYTES
      in OBSERVED;inversion OBSERVED;reflexivity. }
  subst selected;rewrite TAG in LOAD.
  assert(REGION:gateway_native_region_owned native protected word_after word_next).
  { exact(proj2(proj1(proj1 ACTIVE))). }
  assert(ERASED:gateway_value_active native stable base slots stream_block stream_offset final_stream readonly original word_after word_next).
  { eapply gateway_value_active_discipline;[|exact ACTIVE]. intros memory current[SIDE REST];exact SIDE. }
  pose proof(gateway_actual_primitive_branch_memory backend python objects detached io stable thread_errno decimal_float
    runtime constructors references primitive slots arguments initial stream_block stream_offset final_stream readonly original
    protected word_after word_next suffix value after next none_symbol CONSTANTS NONE(conj ERASED LOAD)REGION
    (gateway_value_active_avoids native stable base slots stream_block stream_offset final_stream readonly original
      word_after word_next ERASED)SUFFIX NONNULL)as FINAL.
  exists final_stream;split;[exact STREAM_AFTER|]. split;[|exact(proj1(proj2 FINAL))].
  exact(gateway_value_context_after_native_region backend io native stable base thread_errno runtime
    stream_block stream_offset final_stream readonly original word_after word_next after next(proj1 ERASED)FINAL).
Qed.

End PrimitiveStream.
