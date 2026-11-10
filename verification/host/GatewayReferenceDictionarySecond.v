(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The same dictionary retains its parent and key owners while
   its checked duplicate guard selects a strictly shorter second recursive source call. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Machine CallContexts.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayPython GatewayObjects
  GatewayObjectDiscipline GatewayObjectThreads GatewayValue GatewayValueEntry GatewayValueContext GatewayValueStack
  GatewayContainerLength GatewayContainerGuards GatewayContainerMemory GatewayContainerLoopSource
  GatewayContainerDictionarySource GatewayContainerChildContext GatewayArrayBindings GatewayDictionarySecondReceipt
  GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceStackBound GatewayReferenceDictionaryLedger
  GatewayReferenceContainerContext GatewayReferenceThreads GatewayReferenceGraphCapture GatewayReadonly
  GatewayPathEvents GatewayThreadRuntime GatewayStreamInterface.
Import ListNotations.
Open Scope Z_scope.

Theorem gateway_reference_actual_dictionary_second {World Event}(backend:gateway_backend World Event)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (reference_threads:gateway_reference_thread_contract backend(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    context older ledger held parent_ticket parent parent_offset key_ticket key key_offset slots parameters depth index status size
    stream_block stream_offset initial readonly original before world events value after next:
  gateway_reference_stack_bound context older->
  gateway_reference_dictionary_entries context older ledger parent_ticket(Vptr parent parent_offset)key_ticket(Vptr key key_offset)->
  parameters!_container=Some(Vptr parent parent_offset)->parameters!_first=Some(Vptr key key_offset)->
  parameters!_stream=Some(Vptr stream_block stream_offset)->parameters!_depth=Some(Vint depth)->
  parameters!_index__1=Some(Vlong index)->parameters!_string_key=Some(Vint status)->0<Int.signed status->
  gateway_reference_counted_context python objects decimal_float detached stable ledger held gateway_container_object slots
    stream_block stream_offset initial readonly original size before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Returnstate(Vint Int.zero)(gateway_dictionary_contains_cont slots parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  exists called_parameters prefix reading suffix child_before child_world child child_after child_next,
    events=prefix++reading++suffix /\Forall gateway_quiet_event prefix /\(length reading<length events)%nat /\
    called_parameters!_container=Some(Vptr parent parent_offset) /\called_parameters!_first=Some(Vptr key key_offset) /\
    called_parameters!_stream=Some(Vptr stream_block stream_offset) /\called_parameters!_depth=Some(Vint depth) /\
    called_parameters!_index__1=Some(Vlong index) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate(Vint Int.zero)(gateway_dictionary_contains_cont slots parameters)before)world)prefix
      (gateway_live(Callstate(Internal f_host_value)[Vptr stream_block stream_offset;Vint(Int.sub depth Int.one)]
        (gateway_dictionary_second_cont slots called_parameters)child_before)child_world) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Callstate(Internal f_host_value)[Vptr stream_block stream_offset;Vint(Int.sub depth Int.one)]Kstop child_before)child_world)reading
      (gateway_live(Returnstate child Kstop child_after)child_next) /\child<>Vnullptr /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate child(gateway_dictionary_second_cont slots called_parameters)child_after)child_next)suffix
      (gateway_live(Returnstate value Kstop after)next) /\
    gateway_reference_counted_context python objects decimal_float detached stable ledger held gateway_container_object slots
      stream_block stream_offset initial readonly original size child_before child_world /\
    gateway_reference_stack_bound(plug_cont(gateway_dictionary_second_cont slots called_parameters)context)ledger /\
    gateway_reference_source_bound(Clight.globalenv prog)
      (Callstate(Internal f_host_value)[Vptr stream_block stream_offset;Vint(Int.sub depth Int.one)]
        (plug_cont(gateway_dictionary_second_cont slots called_parameters)context)child_before)ledger /\
    gateway_value_context(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)stream_block stream_offset initial
      (gateway_container_child_readonly slots readonly)child_before child_before child_world /\
    (forall candidate position,gateway_container_child_readonly slots readonly candidate position->gateway_native_private(python child_world)candidate).
Proof.
  intros STACK ENTRIES PARENT KEY STREAM DEPTH INDEX STRING_KEY POSITIVE INPUT RUN NONNULL.
  set(property:=gateway_reference_counted_context python objects decimal_float detached stable ledger held gateway_container_object slots
    stream_block stream_offset initial readonly original size).
  pose proof(gateway_reference_counted_context_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation
    runtime reference_threads ledger held gateway_container_object slots stream_block stream_offset initial readonly original size)as CLOSED.
  destruct gateway_actual_recursive_value_binding as[symbol[SYMBOL FUNCTION]].
  destruct(gateway_actual_dictionary_second_receipt backend(Clight.globalenv prog)property slots parameters(Vptr stream_block stream_offset)
    depth status before world events value after next symbol CLOSED STREAM DEPTH ltac:(right;eexists;eexists;reflexivity)
    STRING_KEY POSITIVE SYMBOL FUNCTION INPUT RUN NONNULL)
    as(called_parameters &prefix &reading &suffix &child_before &child_world &child &child_after &child_next &EVENTS &QUIET &SHORT &
      DUPLICATE &CALLED_PARENT &CALLED_KEY &CALLED_STREAM &CALLED_DEPTH &CALLED_INDEX &CALLED &PREFIX &CHILD_RUN &CHILD_NONNULL &REST).
  assert(PARENT_VALUE:called_parameters!_container=Some(Vptr parent parent_offset))by(rewrite CALLED_PARENT;exact PARENT).
  assert(KEY_VALUE:called_parameters!_first=Some(Vptr key key_offset))by(rewrite CALLED_KEY;exact KEY).
  assert(CHILD_STACK:gateway_reference_stack_bound(plug_cont(gateway_dictionary_second_cont slots called_parameters)context)ledger).
  { unfold gateway_dictionary_second_cont;cbn[plug_cont].
    exact(gateway_reference_dictionary_call_stack context older ledger parent_ticket(Vptr parent parent_offset)key_ticket(Vptr key key_offset)
      (Some _t'39)f_host_value(gateway_value_environment slots)called_parameters
      (Kseq gateway_dictionary_bind_child(Kseq gateway_dictionary_after_child gateway_dictionary_iteration_cont))
      STACK ENTRIES eq_refl PARENT_VALUE KEY_VALUE). }
  pose proof(gateway_reference_stack_call_bound(Clight.globalenv prog)(Internal f_host_value)
    [Vptr stream_block stream_offset;Vint(Int.sub depth Int.one)]
    (plug_cont(gateway_dictionary_second_cont slots called_parameters)context)child_before ledger CHILD_STACK)as CHILD_BOUND.
  pose proof CALLED as[COUNTED[SCOPE NATIVE]].
  destruct(gateway_container_child_input backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
    (gateway_python_discipline python objects detached)thread_errno runtime gateway_container_object slots stream_block stream_offset initial readonly original size
    child_before child_world COUNTED NATIVE)as[CHILD_CONTEXT CHILD_NATIVE].
  exists called_parameters,prefix,reading,suffix,child_before,child_world,child,child_after,child_next.
  split;[exact EVENTS|]. split;[exact QUIET|]. split;[exact SHORT|]. split;[exact PARENT_VALUE|]. split;[exact KEY_VALUE|].
  split;[rewrite CALLED_STREAM;exact STREAM|]. split;[rewrite CALLED_DEPTH;exact DEPTH|]. split;[rewrite CALLED_INDEX;exact INDEX|].
  split;[exact PREFIX|]. split;[exact CHILD_RUN|]. split;[exact CHILD_NONNULL|]. split;[exact REST|].
  split;[exact CALLED|]. split;[exact CHILD_STACK|]. split;[exact CHILD_BOUND|]. split;assumption.
Qed.
