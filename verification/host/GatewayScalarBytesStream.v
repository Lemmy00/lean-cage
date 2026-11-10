(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Byte decoding returns its exact stream state as well as its owned payload root. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayObjectDiscipline
  GatewayRootLeases GatewayObjectThreads GatewayValue GatewayValueEntry GatewayValueContext GatewayValueStack GatewayScalarLength
  GatewayScalarBuffer GatewayScalarPayloadMemory GatewayScalarTerminate GatewayScalarSizedFrames GatewayScalarBytesCall
  GatewayScalarReadPath GatewayScalarBytesPath GatewayScalarStreamCleanup GatewayScalarBytes GatewayScalarConstructorCalls GatewayRegionThreads
  GatewayNativeRegions GatewayNativeMemory GatewayObjectEvents GatewayObjectRuns GatewayPathEvents GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Theorem gateway_actual_bytes_stream_value {World Event}(backend:gateway_backend World Event)
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
    slots parameters stream_block stream_offset initial readonly original size object bytes before world events value after next :
  parameters!_bytes=Some(Vptr object Ptrofs.zero) ->Int64.unsigned size<=268435456 ->
  gateway_scalar_payload_ready(fun current candidate=>gateway_native_private(python current)candidate)stable
    (gateway_python_discipline python objects detached)heap_allocation gateway_scalar_bytes slots stream_block stream_offset initial readonly original
    size object bytes before world ->
  (forall candidate position,readonly candidate position ->gateway_native_private(python world)candidate) ->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Returnstate(Vint Int.zero)(gateway_scalar_read_cont slots parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->value<>Vnullptr ->
  (gateway_value_context(fun current candidate=>gateway_native_private(python current)candidate)stable
    (gateway_python_discipline python objects detached)stream_block stream_offset initial readonly original after next /\
    (forall candidate position,readonly candidate position ->gateway_native_private(python next)candidate)) /\
    (exists ticket,gateway_held_values python objects decimal_float leases
      [{|gateway_held_ticket:=ticket;gateway_held_object:=value;gateway_held_view:=gateway_held_scalar_value(gateway_bytes_object bytes)|}]next) /\
    gateway_value_heap decimal_float(objects next)value(gateway_wire_scalar 5 bytes) /\
    gateway_received_bytes io(stream_descriptor initial)events=[].
Proof.
  intros BUFFER MAXIMUM INPUT READONLY RUN NONNULL.
  set(native:=fun current candidate=>gateway_native_private(python current)candidate).
  set(base:=gateway_python_discipline python objects detached).
  set(augmented:=gateway_native_region_discipline native base readonly).
  pose proof(gateway_thread_with_native_region backend io native stable base thread_errno runtime readonly)as THREADS.
  assert(OWNED:gateway_native_region_owned native readonly before world).
  { destruct INPUT as[[[[[[SIDE[STREAM[STABLE[RAW FRAME]]]]SLOTS]TAG]SIZE]REST]PAYLOAD].
    intros candidate position READ;split;
      [exact(gateway_value_readonly_live _ _ _ _ _ RAW candidate position READ)|apply READONLY with(position:=position);exact READ]. }
  assert(AUGMENTED_INPUT:gateway_scalar_payload_ready native stable augmented heap_allocation gateway_scalar_bytes slots stream_block stream_offset
    initial readonly original size object bytes before world).
  { destruct INPUT as[READY PAYLOAD];split;[|exact PAYLOAD]. pose proof READY as[_[[SIDE HEAP]SEPARATE]].
    eapply gateway_scalar_buffer_rebase;[exact READY|split;assumption]. }
  destruct(gateway_actual_bytes_constructor_cut backend io native stable augmented thread_errno THREADS heap_allocation slots parameters
    stream_block stream_offset initial readonly original size object bytes before world events value after next BUFFER AUGMENTED_INPUT RUN NONNULL)
    as(definition &called_parameters &prefix &constructing &suffix &constructor_before &constructor_world &constructor_after &constructor_next &
      DEFINITION &EVENTS &QUIET &CALLED_BUFFER &AUGMENTED_READY &CONSTRUCTOR_RUN &REST).
  pose proof(gateway_scalar_terminated_side native stable augmented heap_allocation gateway_scalar_bytes slots stream_block stream_offset initial readonly original
    size object bytes constructor_before constructor_world AUGMENTED_READY)as[CALLED_SIDE CALLED_OWNED].
  assert(READY:gateway_scalar_private_ready python objects detached stable heap_allocation gateway_scalar_bytes slots stream_block stream_offset
    initial readonly original size object bytes constructor_before constructor_world).
  { split;[eapply gateway_scalar_terminated_rebase;[exact AUGMENTED_READY|exact CALLED_SIDE]|].
    intros candidate position READ;exact(proj2(CALLED_OWNED candidate position READ)). }
  destruct(gateway_actual_scalar_constructor_storage backend(Clight.globalenv prog)python objects detached io stable thread_errno heap_allocation decimal_float leases
    runtime constructors roots object_threads gateway_api_bytes definition[Vptr object Ptrofs.zero;Vlong size](gateway_bytes_object bytes)gateway_bytes_kind
    gateway_scalar_bytes slots stream_block stream_offset initial readonly original size object bytes constructor_before constructor_world constructing value
    constructor_after constructor_next DEFINITION
    ltac:(intros;split;[eapply gateway_scalar_bytes_request;[eassumption|exact MAXIMUM]|exact I])eq_refl eq_refl
    ltac:(unfold gateway_destructor_kind;auto 9)
    READY CONSTRUCTOR_RUN NONNULL)as(ticket &AFTER_READY &HELD).
  destruct(gateway_actual_scalar_stream_cleanup backend python objects decimal_float leases detached io stable thread_errno heap_allocation
    runtime allocations roots object_threads _ _t'22 gateway_scalar_bytes slots called_parameters stream_block stream_offset initial readonly original size object
    constructor_after constructor_next suffix value value after next ltac:(discriminate)CALLED_BUFFER
    (proj1(proj1(proj1 AFTER_READY)))HELD(proj2 AFTER_READY)REST)as[[FINAL[HELD_FINAL FINAL_NATIVE]]CLEANUP_EMPTY].
  split;[split;[exact FINAL|exact FINAL_NATIVE]|]. split;[exists ticket;exact HELD_FINAL|]. split.
  - inversion HELD_FINAL as[|? ? CAPTURED REST_HELD];subst.
    destruct CAPTURED as[LEASE[ROOTED[PRIVATE[DESTRUCTIBLE[DESCRIBED CHILDREN]]]]].
    eapply gateway_heap_scalar;[exact DESCRIBED|apply gateway_scalar_raw_bytes].
  - rewrite EVENTS,!gateway_received_append,(gateway_quiet_received io(stream_descriptor initial)prefix QUIET),CLEANUP_EMPTY.
    rewrite(gateway_object_run_no_direct_receive backend(Clight.globalenv prog)io gateway_api_bytes definition[Vptr object Ptrofs.zero;Vlong size]
      constructor_before constructor_world constructing value constructor_after constructor_next(stream_descriptor initial)io_projection DEFINITION CONSTRUCTOR_RUN).
    reflexivity.
Qed.
