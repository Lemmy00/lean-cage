(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Successful path decoding retains its actual stream and excludes received NUL bytes. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayObjectDiscipline
  GatewayRootLeases GatewayObjectThreads GatewayValue GatewayValueEntry GatewayValueContext GatewayScalarLength GatewayScalarBuffer
  GatewayScalarPayloadMemory GatewayScalarTerminate GatewayScalarSizedFrames GatewayScalarPathCall GatewayScalarPathDecodedStream GatewayScalarScan
  GatewayScalarPathDenied GatewayScalarReadPath GatewayRegionThreads GatewayRegionMemory GatewayNativeRegions GatewayNativeMemory GatewayObjectEvents
  GatewayPathEvents GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_actual_path_stream_value {World Event}(backend:gateway_backend World Event)
    python objects decimal_float leases detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (allocations:gateway_native_memory_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)heap_allocation)
    (constructors:gateway_objects_runtime backend python objects decimal_float)
    (roots:gateway_root_lease_runtime backend python objects decimal_float leases)
    (object_threads:gateway_object_thread_contract backend(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects leases)
    (io_projection:gateway_direct_io_projection backend io)
    slots parameters stream_block stream_offset initial readonly original size object bytes before world events value after next:
  parameters!_bytes=Some(Vptr object Ptrofs.zero) ->Int64.unsigned size<=4095 ->
  gateway_scalar_payload_ready(fun current candidate=>gateway_native_private(python current)candidate)stable
    (gateway_python_discipline python objects detached)heap_allocation gateway_scalar_path slots stream_block stream_offset initial readonly original
    size object bytes before world ->
  (forall candidate position,readonly candidate position ->gateway_native_private(python world)candidate) ->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Returnstate(Vint Int.zero)(gateway_scalar_read_cont slots parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value<>Vnullptr ->
  (gateway_value_context(fun current candidate=>gateway_native_private(python current)candidate)stable
    (gateway_python_discipline python objects detached)stream_block stream_offset initial readonly original after next /\
    (forall candidate position,readonly candidate position ->gateway_native_private(python next)candidate)) /\exists characters ticket,
    gateway_filesystem_text bytes characters /\gateway_held_values python objects decimal_float leases
      [{|gateway_held_ticket:=ticket;gateway_held_object:=value;gateway_held_view:=gateway_held_scalar_value(gateway_unicode_object characters)|}]next /\
    gateway_value_heap decimal_float(objects next)value(gateway_wire_scalar 6 bytes) /\
    gateway_received_bytes io(stream_descriptor initial)events=[].
Proof.
  intros BUFFER MAXIMUM INPUT READONLY RUN NONNULL.
  set(native:=fun current candidate=>gateway_native_private(python current)candidate).
  set(base:=gateway_python_discipline python objects detached).
  set(augmented:=gateway_native_region_discipline native base readonly).
  pose proof(gateway_thread_with_native_region backend io native stable base thread_errno runtime readonly)as THREADS.
  pose proof(gateway_memory_with_native_region backend io native stable base heap_allocation allocations readonly)as MEMORY.
  assert(OWNED:gateway_native_region_owned native readonly before world).
  { destruct INPUT as[[[[[[SIDE[STREAM[STABLE[RAW FRAME]]]]SLOTS]TAG]SIZE]REST]PAYLOAD].
    intros candidate position READ;split;
      [exact(gateway_value_readonly_live _ _ _ _ _ RAW candidate position READ)|apply READONLY with(position:=position);exact READ]. }
  assert(AUGMENTED_INPUT:gateway_scalar_payload_ready native stable augmented heap_allocation gateway_scalar_path slots stream_block stream_offset
    initial readonly original size object bytes before world).
  { destruct INPUT as[READY PAYLOAD];split;[|exact PAYLOAD]. pose proof READY as[_[[SIDE HEAP]SEPARATE]].
    eapply gateway_scalar_buffer_rebase;[exact READY|split;assumption]. }
  destruct(gateway_actual_path_scan_cut backend io native stable augmented thread_errno THREADS heap_allocation slots parameters
    stream_block stream_offset initial readonly original size object bytes before world events value after next BUFFER AUGMENTED_INPUT RUN)
    as(called_parameters &prefix &scanning &suffix &scan_before &scan_world &scanned &after_scan &scan_next &
      EVENTS &QUIET &CALLED_BUFFER &CALLED_NULL &SCAN_READY &SCAN_RUN &REST).
  destruct(gateway_actual_scalar_scan backend(Clight.globalenv prog)io native stable augmented thread_errno heap_allocation THREADS MEMORY
    gateway_scalar_path slots stream_block stream_offset initial readonly original size object bytes scan_before scan_world scanning scanned after_scan scan_next
    (stream_descriptor initial)SCAN_READY SCAN_RUN)as[AFTER_SCAN[SCANNED SCAN_EMPTY]].
  assert(NULL:scanned=Vnullptr).
  { inversion SCANNED;subst;[reflexivity|].
    exfalso;apply NONNULL;eapply gateway_actual_nul_path_denied;
      [exact THREADS|exact CALLED_NULL|reflexivity|exact AFTER_SCAN|exact REST]. }
  subst scanned.
  pose proof(gateway_scalar_terminated_side native stable augmented heap_allocation gateway_scalar_path slots stream_block stream_offset initial readonly original
    size object bytes after_scan scan_next AFTER_SCAN)as[AFTER_SIDE AFTER_OWNED].
  assert(BASE_READY:gateway_scalar_terminated_ready native stable base heap_allocation gateway_scalar_path slots stream_block stream_offset initial readonly
    original size object bytes after_scan scan_next).
  { eapply gateway_scalar_terminated_rebase;[exact AFTER_SCAN|exact AFTER_SIDE]. }
  destruct(gateway_actual_path_decoded_stream_value backend python objects decimal_float leases detached io stable thread_errno heap_allocation runtime allocations
    constructors roots object_threads io_projection slots called_parameters stream_block stream_offset initial readonly original size object bytes after_scan scan_next
    suffix value after next CALLED_BUFFER MAXIMUM SCANNED BASE_READY
    ltac:(intros candidate position READ;exact(proj2(AFTER_OWNED candidate position READ)))REST NONNULL)
    as[FINAL[characters[ticket[DECODED[HELD[HEAP FINAL_EMPTY]]]]]].
  split;[exact FINAL|]. exists characters,ticket;split;[exact DECODED|]. split;[exact HELD|]. split;[exact HEAP|].
  rewrite EVENTS,!gateway_received_append,(gateway_quiet_received io(stream_descriptor initial)prefix QUIET),SCAN_EMPTY,FINAL_EMPTY;reflexivity.
Qed.
