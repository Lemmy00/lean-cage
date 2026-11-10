(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Primitive values return their same stream for the next actual child call. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayRootLeases
  GatewayObjectDiscipline GatewayObjectThreads GatewayValue GatewayObjectConstants GatewayValueEntry GatewayValueContext GatewayValueStack
  GatewayValueActual GatewayValueRegions GatewayPrimitiveValues GatewayPrimitiveMemory GatewayValueNodeMemory GatewayValueReturnContext
  GatewayNativeRegions GatewayRegionThreads GatewayNativeRoots GatewayObjectEvents GatewayStreamInterface GatewayThreadRuntime GatewayPathEvents.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_actual_primitive_stream_value {World Event}(backend:gateway_backend World Event)
    python objects detached io stable thread_errno heap_allocation decimal_float leases
    (runtime:gateway_thread_runtime backend io(fun world object=>gateway_native_private(python world)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (constructors:gateway_objects_runtime backend python objects decimal_float)
    (references:gateway_reference_runtime backend python objects)
    (roots:gateway_root_lease_runtime backend python objects decimal_float leases)
    (object_threads:gateway_object_thread_contract backend(fun world object=>gateway_native_private(python world)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects leases)
    (projection:gateway_direct_io_projection backend io)
    primitive byte remaining arguments before world events value after next stream_block stream_offset initial readonly original none_symbol:
  gateway_none_runtime python objects(Vptr none_symbol Ptrofs.zero) ->
  Genv.find_symbol(Clight.globalenv prog)__Py_NoneStruct=Some none_symbol ->
  Byte.unsigned byte=gateway_primitive_tag primitive ->gateway_value_stream arguments=Vptr stream_block stream_offset ->
  gateway_value_context(fun world object=>gateway_native_private(python world)object)stable
    (gateway_python_discipline python objects detached)stream_block stream_offset initial readonly original before world ->
  (forall object position,readonly object position ->gateway_native_private(python world)object) ->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_value)(gateway_value_arguments_list arguments)Kstop before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value<>Vnullptr ->
  gateway_received_bytes io(stream_descriptor initial)events=byte::remaining ->
  exists final_stream ticket,
    gateway_stream_read_after(gateway_stream_node_debit initial)1 final_stream /\
    gateway_value_context(fun world object=>gateway_native_private(python world)object)stable
      (gateway_python_discipline python objects detached)stream_block stream_offset final_stream readonly original after next /\
    (forall object position,readonly object position ->gateway_native_private(python next)object) /\
    gateway_held_values python objects decimal_float leases
      [{|gateway_held_ticket:=ticket;gateway_held_object:=value;
        gateway_held_view:=gateway_held_scalar_value(gateway_primitive_object primitive)|}]next /\
    gateway_value_heap decimal_float(objects next)value(gateway_primitive_wire primitive) /\
    gateway_received_bytes io(stream_descriptor initial)events=[byte].
Proof.
  intros CONSTANTS NONE TAG STREAM INPUT READONLY RUN NONNULL OBSERVED.
  set(native:=fun world object=>gateway_native_private(python world)object).
  set(base:=gateway_python_discipline python objects detached).
  destruct(gateway_actual_primitive_value backend python objects detached io stable thread_errno heap_allocation decimal_float leases
    runtime constructors references roots object_threads projection primitive byte remaining arguments before world events value after next
    stream_block stream_offset initial readonly original none_symbol CONSTANTS NONE TAG STREAM INPUT RUN NONNULL OBSERVED)
    as(ticket &HELD &HEAP &SIDE &BYTES).
  set(augmented:=gateway_native_region_discipline native base readonly).
  pose proof(gateway_thread_with_native_region backend io native stable base thread_errno runtime readonly)as THREADS.
  assert(AUGMENTED_INPUT:gateway_value_context native stable augmented stream_block stream_offset initial readonly original before world).
  { pose proof INPUT as[SIDE_READY CONTEXT];split;[split;[exact SIDE_READY|]|exact CONTEXT].
    assert(ALL:gateway_native_region_owned native(gateway_value_input_region stream_block stream_offset readonly)before world)
      by(eapply gateway_value_return_native_region;[exact INPUT|exact READONLY]).
    intros object position READONLY_POINT;exact(ALL object position(or_intror READONLY_POINT)). }
  destruct(gateway_actual_value_tag backend io native stable augmented thread_errno THREADS arguments before world events value after next
    stream_block stream_offset initial readonly original STREAM AUGMENTED_INPUT RUN NONNULL)
    as(slots &selected &prefix &reading &suffix &word_before &word_world &word_after &word_next &final_stream &
      EVENTS &DEPTH &NODES &QUIET &PREFIX &ALLOCATED &READ &READ_BYTES &LOAD &STREAM_AFTER &ACTIVE &SUFFIX).
  assert(SELECTED:selected=byte).
  { rewrite EVENTS,!gateway_received_append,(gateway_quiet_received io(stream_descriptor initial)prefix QUIET),READ_BYTES
      in OBSERVED;inversion OBSERVED;reflexivity. }
  subst selected;rewrite TAG in LOAD.
  pose proof ACTIVE as[[[CALLED_SIDE CALLED_OWNED]CONTEXT]STACK].
  assert(BASE_ACTIVE:gateway_value_active native stable base slots stream_block stream_offset final_stream readonly original word_after word_next).
  { split;[split;[exact CALLED_SIDE|exact CONTEXT]|exact STACK]. }
  set(protected:=gateway_value_input_region stream_block stream_offset readonly).
  assert(OWNED:gateway_native_region_owned native protected word_after word_next).
  { eapply gateway_value_return_native_region;[exact(proj1 BASE_ACTIVE)|].
    intros object position READONLY_POINT;exact(proj2(CALLED_OWNED object position READONLY_POINT)). }
  pose proof(gateway_actual_primitive_branch_memory backend python objects detached io stable thread_errno decimal_float runtime constructors references
    primitive slots arguments initial stream_block stream_offset final_stream readonly original protected word_after word_next suffix value after next
    none_symbol CONSTANTS NONE(conj BASE_ACTIVE LOAD)OWNED
    (gateway_value_environment_avoids_inputs native stable base slots stream_block stream_offset final_stream readonly original word_after word_next BASE_ACTIVE)
    SUFFIX NONNULL)as[FINAL_SIDE[FINAL_OWNED FRAME]].
  exists final_stream,ticket;split;[exact STREAM_AFTER|]. split.
  - eapply gateway_value_context_return_frame;[exact runtime|exact(proj1 BASE_ACTIVE)|exact FINAL_SIDE|exact FINAL_OWNED|exact FRAME].
  - split;[intros object position READONLY_POINT;exact(proj2(FINAL_OWNED object position(or_intror READONLY_POINT)))|].
    split;[exact HELD|]. split;assumption.
Qed.
