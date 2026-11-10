(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual scalar cleanup retains its stream and selected source references. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayPython GatewayObjects GatewayObjectDiscipline
  GatewayObjectThreads GatewayReferences GatewayValueEntry GatewayValueEnvironment GatewayScalarLength
  GatewayScalarBuffer GatewayScalarSizedFrames GatewayScalarFree GatewayScalarBytesPath GatewayScalarCleanup GatewaySourcePaths
  GatewayFramedRuntime GatewayCallerReturns GatewayMemoryBindings GatewayNativeMemory GatewayPathEvents GatewayValueContext GatewayValueStack GatewayValueReturnContext GatewayNativeRegions GatewayRegionThreads GatewayRegionMemory
  GatewayReturnMemory GatewayStreamInterface GatewayThreadRuntime GatewayThreadInvariant
  GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceHeld GatewayReferenceThreads.
Import ListNotations.

Theorem gateway_reference_actual_scalar_cleanup {World Event}(backend:gateway_backend World Event)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (allocations:gateway_native_memory_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)heap_allocation)
    (reference_threads:gateway_reference_thread_contract backend(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    ledger held identifier scalar slots parameters stream_block stream_offset initial readonly original size object before world events returned value after next :
  identifier<>_bytes ->parameters!_bytes=Some(Vptr object Ptrofs.zero) ->
  gateway_scalar_buffer_ready(fun current candidate=>gateway_native_private(python current)candidate)stable
    (gateway_python_discipline python objects detached)heap_allocation scalar slots stream_block stream_offset initial readonly original size object before world ->
  gateway_reference_scope python objects decimal_float ledger held world ->
  (forall candidate position,readonly candidate position ->gateway_native_private(python world)candidate) ->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Returnstate returned(gateway_scalar_constructor_cont identifier slots parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next) ->
  value=returned /\
  (gateway_value_context(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)stream_block stream_offset initial readonly original after next /\
    gateway_reference_scope python objects decimal_float ledger held next /\
    (forall candidate position,readonly candidate position ->gateway_native_private(python next)candidate)) /\
    gateway_received_bytes io(stream_descriptor initial)events=[].
Proof.
  intros DISTINCT BUFFER INPUT HELD READONLY RUN.
  set(native:=fun current candidate=>gateway_native_private(python current)candidate).
  set(base:=gateway_python_discipline python objects detached).
  set(held_base:=gateway_thread_invariant_discipline base(gateway_reference_scope python objects decimal_float ledger held)).
  set(protected:=gateway_value_input_region stream_block stream_offset readonly).
  set(augmented:=gateway_native_region_discipline native held_base protected).
  pose proof(gateway_thread_with_reference_scope backend io native stable base thread_errno heap_allocation python objects decimal_float
    reference_threads ledger held runtime)as HELD_THREADS.
  pose proof(gateway_memory_with_reference_scope backend io native stable base heap_allocation python objects decimal_float
    reference_threads ledger held allocations)as HELD_MEMORY.
  pose proof(gateway_thread_with_native_region backend io native stable held_base thread_errno HELD_THREADS protected)as THREADS.
  pose proof(gateway_memory_with_native_region backend io native stable held_base heap_allocation HELD_MEMORY protected)as MEMORY.
  set(ready:=gateway_scalar_buffer_ready native stable augmented heap_allocation scalar slots stream_block stream_offset initial readonly original size object).
  assert(OWNED:gateway_native_region_owned native protected before world).
  { eapply gateway_value_return_native_region;[exact(proj1(proj1(proj1(proj1 INPUT))))|exact READONLY]. }
  assert(READY:ready before world).
  { pose proof INPUT as[_[[SIDE HEAP]SEPARATE]].
    eapply gateway_scalar_buffer_rebase;[exact INPUT|]. split;[split;[exact SIDE|exact HELD]|exact OWNED]. }
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
  pose proof(gateway_value_environment_avoids_inputs native stable augmented slots stream_block stream_offset initial readonly original free_after free_next
    (proj1(proj1 SIZED)))as AVOIDS.
  destruct(gateway_actual_caller_return_memory backend(Clight.globalenv prog)io native stable augmented thread_errno THREADS None
    f_host_value None(gateway_value_environment slots)called_parameters
    (Some(Etempvar _value(tptr(Tstruct __object noattr))))(Kseq gateway_value_after_scalar Kstop)protected free_after
    free_after free_next suffix free_value value after next eq_refl AVOIDS
    (conj RETURN_READY(conj(proj2(proj1 RETURN_READY))(Mem.unchanged_on_refl _ _)))REST)
    as[[[FINAL_SIDE FINAL_HELD]FINAL_OWNED][FINAL_OWNED_AGAIN FINAL_FRAME]].
  pose proof(proj2(gateway_actual_caller_return_side backend(Clight.globalenv prog)io native stable augmented thread_errno THREADS None
    f_host_value None(gateway_value_environment slots)called_parameters
    (Some(Etempvar _value(tptr(Tstruct __object noattr))))(Kseq gateway_value_after_scalar Kstop)free_after free_next suffix free_value value after next
    eq_refl RETURN_READY REST))as QUIET_RETURN.
  assert(FINAL_CONTEXT:gateway_value_context native stable base stream_block stream_offset initial readonly original after next).
  { eapply gateway_value_context_return_frame;[exact runtime| |exact FINAL_SIDE|exact FINAL_OWNED|exact FINAL_FRAME].
    pose proof(proj1(proj1(proj1 SIZED)))as[CONTEXT_SIDED CONTEXT];split;[exact(proj1(proj1 CONTEXT_SIDED))|exact CONTEXT]. }
  split;[exact(gateway_actual_scalar_final_return backend(Clight.globalenv prog)slots called_parameters returned free_value
    free_after free_next suffix value after next SELECTED REST)|].
  split;[split;[exact FINAL_CONTEXT|split;[exact FINAL_HELD|]]|].
  - intros candidate position READ;exact(proj2(FINAL_OWNED candidate position(or_intror READ))).
  - rewrite EVENTS,REST_EVENTS,!gateway_received_append,(gateway_quiet_received io(stream_descriptor initial)prefix QUIET),
    EMPTY,(gateway_quiet_received io(stream_descriptor initial)suffix QUIET_RETURN);reflexivity.
Qed.
