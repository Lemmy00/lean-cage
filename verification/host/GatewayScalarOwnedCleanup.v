(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Source-owned scalar references survive their actual native buffer cleanup. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayPython GatewayObjects GatewayObjectDiscipline
  GatewayRootLeases GatewayObjectThreads GatewayReferences GatewayValueEntry GatewayValueEnvironment GatewayScalarLength
  GatewayScalarBuffer GatewayScalarSizedFrames GatewayScalarFree GatewayScalarBytesPath GatewayScalarCleanup GatewaySourcePaths
  GatewayFramedRuntime GatewayCallerReturns GatewayMemoryBindings GatewayNativeMemory GatewayPathEvents GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.

Theorem gateway_actual_scalar_owned_cleanup {World Event}(backend:gateway_backend World Event)
    python objects decimal_float leases detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (allocations:gateway_native_memory_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)heap_allocation)
    (roots:gateway_root_lease_runtime backend python objects decimal_float leases)
    (object_threads:gateway_object_thread_contract backend(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects leases)
    held identifier scalar slots parameters stream_block stream_offset initial readonly original size object before world events returned value after next :
  identifier<>_bytes ->parameters!_bytes=Some(Vptr object Ptrofs.zero) ->
  gateway_scalar_buffer_ready(fun current candidate=>gateway_native_private(python current)candidate)stable
    (gateway_python_discipline python objects detached)heap_allocation scalar slots stream_block stream_offset initial readonly original size object before world ->
  gateway_held_values python objects decimal_float leases held world ->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Returnstate returned(gateway_scalar_constructor_cont identifier slots parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->
  (gateway_objects_ready(python next)(objects next)after /\gateway_held_values python objects decimal_float leases held next) /\
    gateway_received_bytes io(stream_descriptor initial)events=[].
Proof.
  intros DISTINCT BUFFER INPUT HELD RUN.
  set(native:=fun current candidate=>gateway_native_private(python current)candidate).
  set(base:=gateway_python_discipline python objects detached).
  set(augmented:=gateway_held_discipline base python objects decimal_float leases held).
  pose proof(gateway_thread_with_held_values backend io native stable base thread_errno heap_allocation python objects decimal_float leases
    roots held runtime object_threads)as THREADS.
  pose proof(gateway_memory_with_held_values backend io native stable base heap_allocation python objects decimal_float leases
    roots held allocations object_threads)as MEMORY.
  set(ready:=gateway_scalar_buffer_ready native stable augmented heap_allocation scalar slots stream_block stream_offset initial readonly original size object).
  assert(READY:ready before world).
  { pose proof INPUT as[_[[SIDE HEAP]SEPARATE]].
    eapply gateway_scalar_buffer_rebase;[exact INPUT|]. split;[exact SIDE|exact HELD]. }
  pose proof(gateway_scalar_buffer_ambient backend io native stable augmented thread_errno THREADS heap_allocation scalar slots
    stream_block stream_offset initial readonly original size object)as CLOSED.
  destruct(gateway_actual_memory_binding gateway_free_api)as[definition[DEFINITION[symbol[SYMBOL FUNCTION]]]].
  destruct gateway_native_memory_actual_abis as[_[FREE _]].
  rewrite FREE in DEFINITION;inversion DEFINITION;subst definition.
  destruct(gateway_scalar_cleanup_path backend(Clight.globalenv prog)ready identifier slots parameters object returned before symbol
    CLOSED DISTINCT BUFFER SYMBOL FUNCTION)as(called_parameters &PATH &CALLED_BUFFER &SELECTED).
  destruct(gateway_source_path_cut backend(Clight.globalenv prog)_ _ _ _ _ _ PATH before world events value after next READY RUN)
    as(prefix &rest &free_before &free_world &EVENTS &QUIET &PREFIX &CALLED &FROM_FREE).
  destruct(gateway_return_cut backend(Clight.globalenv prog)(External EF_free[tptr tvoid]tvoid cc_default)[Vptr object Ptrofs.zero]
    (gateway_scalar_free_cont slots called_parameters)free_before free_world rest(Returnstate value Kstop after)next
    ltac:(cbn;exact I)ltac:(cbn;lia)FROM_FREE)
    as(freeing &suffix &free_value &free_after &free_next &REST_EVENTS &FREE_RUN &REST).
  destruct(gateway_actual_scalar_free backend(Clight.globalenv prog)io native stable augmented thread_errno heap_allocation THREADS MEMORY
    scalar slots stream_block stream_offset initial readonly original size object free_before free_world freeing free_value free_after free_next
    CALLED FREE_RUN)as[UNDEFINED[SIZED EMPTY]].
  pose proof(gateway_value_active_environment native stable augmented slots stream_block stream_offset initial readonly original free_after free_next
    (proj1(proj1 SIZED)))as RETURN_READY.
  destruct(gateway_actual_caller_return_side backend(Clight.globalenv prog)io native stable augmented thread_errno THREADS None
    f_host_value None(gateway_value_environment slots)called_parameters
    (Some(Etempvar _value(tptr(Tstruct __object noattr))))(Kseq gateway_value_after_scalar Kstop)free_after free_next suffix free_value value after next
    eq_refl RETURN_READY REST)as[FINAL QUIET_RETURN].
  split;[exact FINAL|].
  rewrite EVENTS,REST_EVENTS,!gateway_received_append,(gateway_quiet_received io(stream_descriptor initial)prefix QUIET),
    EMPTY,(gateway_quiet_received io(stream_descriptor initial)suffix QUIET_RETURN);reflexivity.
Qed.
