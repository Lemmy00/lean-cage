(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Whole byte decoding returns the same caller stream after its actual reads and cleanup. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Machine.
From LeanImport Require Import Lean.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayObjectDiscipline
  GatewayRootLeases GatewayObjectThreads GatewayValue GatewayValueEntry GatewayValueContext GatewayValueStack GatewayValueActual
  GatewayValueNodeMemory GatewayValueTag GatewayScalarLength GatewayScalarContext GatewayScalarSize GatewayScalarBuffer GatewayScalarPayload
  GatewayScalarPayloadMemory GatewayScalarSizedFrames GatewayScalarBytesStream GatewayValueStreamRelations GatewayScalarAllocationPath GatewayScalarReadPath GatewayScalarReadMemory
  GatewayNativeRegions GatewayRegionThreads GatewayRegionMemory GatewayNativeMemory GatewayNoMemory GatewayObjectEvents
  GatewayImport GatewayScalarEncoding GatewayWordValues GatewayPathEvents GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Theorem gateway_actual_received_bytes_stream_value {World Event}(backend:gateway_backend World Event)
    python objects decimal_float leases detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (allocations:gateway_native_memory_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)heap_allocation)
    (constructors:gateway_objects_runtime backend python objects decimal_float)
    (roots:gateway_root_lease_runtime backend python objects decimal_float leases)
    (object_threads:gateway_object_thread_contract backend(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects leases)
    (errors:gateway_no_memory_runtime backend python)(io_projection:gateway_direct_io_projection backend io)
    arguments before world events value after next stream_block stream_offset initial readonly original byte remaining :
  Byte.unsigned byte=5 ->gateway_value_stream arguments=Vptr stream_block stream_offset ->
  gateway_value_context(fun current candidate=>gateway_native_private(python current)candidate)stable
    (gateway_python_discipline python objects detached)stream_block stream_offset initial readonly original before world ->
  (forall candidate position,readonly candidate position ->gateway_native_private(python world)candidate) ->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_value)(gateway_value_arguments_list arguments)Kstop before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value<>Vnullptr ->
  gateway_received_bytes io(stream_descriptor initial)events=byte::remaining ->
  exists final_stream,
    (gateway_value_context(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)stream_block stream_offset final_stream readonly original after next /\
      (forall candidate position,readonly candidate position ->gateway_native_private(python next)candidate)) /\
    exists size_bytes payload ticket,
    length size_bytes=8%nat /\gateway_decoded_value size_bytes=Z.of_nat(length payload) /\
    gateway_received_bytes io(stream_descriptor initial)events=byte::(size_bytes++payload) /\
    gateway_scalar_stream_after initial 8(Z.of_nat(length payload))final_stream /\
    gateway_held_values python objects decimal_float leases
      [{|gateway_held_ticket:=ticket;gateway_held_object:=value;gateway_held_view:=gateway_held_scalar_value(gateway_bytes_object payload)|}]next /\
    gateway_value_heap decimal_float(objects next)value(gateway_wire_scalar 5 payload).
Proof.
  intros TAG STREAM INPUT READONLY RUN NONNULL OBSERVED.
  set(native:=fun current candidate=>gateway_native_private(python current)candidate).
  set(base:=gateway_python_discipline python objects detached).
  set(augmented:=gateway_native_region_discipline native base readonly).
  pose proof(gateway_thread_with_native_region backend io native stable base thread_errno runtime readonly)as THREADS.
  pose proof(gateway_memory_with_native_region backend io native stable base heap_allocation allocations readonly)as MEMORY.
  assert(OWNED:gateway_native_region_owned native readonly before world).
  { destruct INPUT as[SIDE[PRIVATE[STABLE[RAW FRAME]]]].
    intros candidate position READ;split;
      [exact(gateway_value_readonly_live _ _ _ _ _ RAW candidate position READ)|apply READONLY with(position:=position);exact READ]. }
  assert(AUGMENTED_INPUT:gateway_value_context native stable augmented stream_block stream_offset initial readonly original before world).
  { destruct INPUT as[SIDE REST];split;[split;assumption|exact REST]. }
  destruct(gateway_actual_value_tag backend io native stable augmented thread_errno THREADS arguments before world events value after next
    stream_block stream_offset initial readonly original STREAM AUGMENTED_INPUT RUN NONNULL)
    as(slots &selected &tag_prefix &tag_read &tag_suffix &tag_before &tag_world &tag_after &tag_next &tag_stream &
      EVENTS &DEPTH &NODES &TAG_QUIET &TAG_PREFIX &ALLOCATED &TAG_RUN &TAG_OBSERVED &TAG_LOAD &TAG_STREAM &TAG_ACTIVE &TAG_REST).
  assert(SELECTED:selected=byte).
  { rewrite EVENTS,!gateway_received_append,(gateway_quiet_received io(stream_descriptor initial)tag_prefix TAG_QUIET),TAG_OBSERVED in OBSERVED.
    inversion OBSERVED;reflexivity. }
  subst selected;rewrite TAG in TAG_LOAD.
  destruct(gateway_actual_scalar_size backend io native stable augmented thread_errno THREADS gateway_scalar_bytes slots arguments initial
    stream_block stream_offset tag_stream readonly original tag_after tag_next tag_suffix value after next STREAM(conj TAG_ACTIVE TAG_LOAD)TAG_REST NONNULL)
    as(size_parameters &size_bytes &size_prefix &size_read &size_suffix &size_before &size_world &size_after &size_next &size_stream &
      SIZE_EVENTS &SIZE_QUIET &SIZE_PARAMETER &SIZE_DEPTH &SIZE_PREFIX &SIZE_RUN &SIZE_OBSERVED &SIZE_COUNT &SIZE_LOAD &SIZE_STREAM &SIZE_ACTIVE &SIZE_REST).
  set(size:=Int64.repr(gateway_decoded_value size_bytes)).
  assert(SIZE_WIDTH:length size_bytes=8%nat)by(change(Z.of_nat(length size_bytes)=8)in SIZE_COUNT;lia).
  destruct(gateway_actual_scalar_buffer_context backend python objects detached io native stable thread_errno heap_allocation augmented runtime THREADS MEMORY errors
    gateway_scalar_bytes slots arguments size_parameters stream_block stream_offset size_stream readonly original size size_after size_next size_suffix value after next
    ltac:(intros memory current[SIDE HELD];exact SIDE)STREAM SIZE_PARAMETER(conj SIZE_ACTIVE SIZE_LOAD)SIZE_REST NONNULL)
    as(MAXIMUM &object &malloc_parameters &allocation_prefix &allocating &allocation_suffix &malloc_before &malloc_world &malloc_after &malloc_next &
      ALLOCATION_EVENTS &ALLOCATION_QUIET &MALLOC_PARAMETER &MALLOC_RUN &MALLOC_READY &ALLOCATION_EMPTY &ALLOCATION_REST).
  destruct(gateway_actual_scalar_payload backend io native stable augmented thread_errno THREADS heap_allocation gateway_scalar_bytes slots arguments
    malloc_parameters stream_block stream_offset size_stream readonly original size object malloc_after malloc_next allocation_suffix value after next
    STREAM MALLOC_PARAMETER MALLOC_READY ALLOCATION_REST NONNULL)
    as(read_parameters &payload_prefix &payload_read &payload_suffix &payload_before &payload_world &payload_after &payload_next &payload &payload_stream &
      PAYLOAD_EVENTS &PAYLOAD_QUIET &READ_STREAM &READ_BUFFER &READ_RUN &RECEIPT &PAYLOAD_STREAM &PAYLOAD_READY &PAYLOAD_REST).
  pose proof PAYLOAD_READY as[_[[[PAYLOAD_SIDE PAYLOAD_OWNED]HEAP]SEPARATE]].
  pose proof RECEIPT as[PAYLOAD_COUNT PAYLOAD_FITS PAYLOAD_OBSERVED PAYLOAD_LOAD DATA_PERMISSIONS STREAM_PERMISSIONS FINAL_STREAM READ_FRAME].
  assert(BASE_READY:gateway_scalar_payload_ready native stable base heap_allocation gateway_scalar_bytes slots stream_block stream_offset payload_stream readonly original
    size object payload payload_after payload_next).
  { split;[eapply gateway_scalar_buffer_rebase;[exact PAYLOAD_READY|exact PAYLOAD_SIDE]|].
    split;[exact PAYLOAD_COUNT|exact PAYLOAD_LOAD]. }
  destruct(gateway_actual_bytes_stream_value backend python objects decimal_float leases detached io stable thread_errno heap_allocation runtime allocations constructors roots
    object_threads io_projection slots read_parameters stream_block stream_offset payload_stream readonly original size object payload payload_after payload_next
    payload_suffix value after next READ_BUFFER MAXIMUM BASE_READY
    ltac:(intros candidate position READ;exact(proj2(PAYLOAD_OWNED candidate position READ)))PAYLOAD_REST NONNULL)
    as[[FINAL FINAL_NATIVE][[ticket HELD][HEAP_VALUE FINAL_EMPTY]]].
  assert(TAG_DESCRIPTOR:stream_descriptor tag_stream=stream_descriptor initial)by(exact(proj1 TAG_STREAM)).
  assert(SIZE_DESCRIPTOR:stream_descriptor size_stream=stream_descriptor initial).
  { rewrite(proj1 SIZE_STREAM);exact TAG_DESCRIPTOR. }
  assert(PAYLOAD_DESCRIPTOR:stream_descriptor payload_stream=stream_descriptor initial).
  { rewrite(proj1 PAYLOAD_STREAM);exact SIZE_DESCRIPTOR. }
  assert(SIZE_VALUE:gateway_decoded_value size_bytes=Z.of_nat(length payload)).
  { pose proof PAYLOAD_COUNT as COUNT.
    unfold size in COUNT;rewrite gateway_decoded_unsigned in COUNT by lia;lia. }
  assert(EXACT_BYTES:gateway_received_bytes io(stream_descriptor initial)events=byte::(size_bytes++payload)).
  { rewrite EVENTS,SIZE_EVENTS,ALLOCATION_EVENTS,PAYLOAD_EVENTS,!gateway_received_append,
      (gateway_quiet_received io(stream_descriptor initial)tag_prefix TAG_QUIET),TAG_OBSERVED,
      (gateway_quiet_received io(stream_descriptor initial)size_prefix SIZE_QUIET),
      <-TAG_DESCRIPTOR,SIZE_OBSERVED,TAG_DESCRIPTOR,
      (gateway_quiet_received io(stream_descriptor initial)allocation_prefix ALLOCATION_QUIET),
      <-SIZE_DESCRIPTOR,ALLOCATION_EMPTY,SIZE_DESCRIPTOR,
      (gateway_quiet_received io(stream_descriptor initial)payload_prefix PAYLOAD_QUIET),
      <-SIZE_DESCRIPTOR,PAYLOAD_OBSERVED,SIZE_DESCRIPTOR,
      <-PAYLOAD_DESCRIPTOR,FINAL_EMPTY;cbn;repeat rewrite app_nil_r;reflexivity. }
  exists payload_stream;split;[split;[exact FINAL|exact FINAL_NATIVE]|]. exists size_bytes,payload,ticket.
  split;[exact SIZE_WIDTH|]. split;[exact SIZE_VALUE|]. split;[exact EXACT_BYTES|]. split.
  - exists tag_stream,size_stream;split;[exact TAG_STREAM|]. split;[exact SIZE_STREAM|]. rewrite PAYLOAD_COUNT;exact PAYLOAD_STREAM.
  - split;assumption.
Qed.
