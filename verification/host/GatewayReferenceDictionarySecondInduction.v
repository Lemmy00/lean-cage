(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual second recursion receives the same retained key and
   parent snapshots, saved source owners and enclosing initialized native cells. *)
From Stdlib Require Import ZArith List Lia.
Local Open Scope Z_scope.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Machine CallContexts.
From HostGateway Require Import GatewaySource GatewayMachine GatewayContexts GatewayPython GatewayObjects GatewayObjectDiscipline GatewayObjectThreads
  GatewayValue GatewayValueEntry GatewayValueContext GatewayValueStack GatewayContainerLength GatewayContainerGuards GatewayContainerMemory
  GatewayContainerLoopSource GatewayContainerChildReceipt GatewayContainerChildContext GatewayArrayBindings
  GatewayReferenceDictionarySecond GatewayContainerDictionarySource GatewayReferenceDictionaryLedger GatewayReferenceParserInputs GatewayReferenceParseResult GatewayReferenceValueProperties GatewayScalarDecoding GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceStackBound GatewayReferenceLoopLedger GatewayReferenceContainerContext
  GatewayReferenceThreads GatewayReferenceGraphCapture GatewayReadonly GatewayPathEvents GatewayThreadRuntime GatewayStreamInterface.
Import ListNotations.

Theorem gateway_reference_actual_dictionary_second_induction {World Event}(backend:gateway_backend World Event)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (reference_threads:gateway_reference_thread_contract backend(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    mode_symbol run_limit context older ledger held parent_ticket parent parent_offset key_ticket key key_offset slots parameters depth index status size stream_block stream_offset initial readonly original
    before world events value after next:
  gateway_reference_short_parser backend python objects decimal_float detached io stable mode_symbol run_limit->
  gateway_reference_ledger_well_formed ledger->gateway_reference_graphs_only held->
  gateway_unicode_strict_mode original(Vptr mode_symbol Ptrofs.zero)->
  (forall object position,gateway_scalar_mode_region mode_symbol object position->readonly object position)->
  (length events<=run_limit)%nat->gateway_reference_stack_bound context older->
  gateway_reference_dictionary_entries context older ledger parent_ticket(Vptr parent parent_offset)key_ticket(Vptr key key_offset)->
  parameters!_container=Some(Vptr parent parent_offset)->parameters!_first=Some(Vptr key key_offset)->parameters!_stream=Some(Vptr stream_block stream_offset)->
  parameters!_depth=Some(Vint depth)->parameters!_index__1=Some(Vlong index)->parameters!_string_key=Some(Vint status)->0<Int.signed status->
  gateway_reference_counted_context python objects decimal_float detached stable ledger held gateway_container_object slots
    stream_block stream_offset initial readonly original size before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Returnstate(Vint Int.zero)(gateway_dictionary_contains_cont slots parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  exists called_parameters prefix reading suffix child_before child_world child child_after child_next,
    events=prefix++reading++suffix /\Forall gateway_quiet_event prefix /\(length reading<length events)%nat /\
    called_parameters!_container=Some(Vptr parent parent_offset) /\called_parameters!_first=Some(Vptr key key_offset) /\called_parameters!_stream=Some(Vptr stream_block stream_offset) /\
    called_parameters!_depth=Some(Vint depth) /\called_parameters!_index__1=Some(Vlong index) /\
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
    (forall candidate position,gateway_container_child_readonly slots readonly candidate position->gateway_native_private(python child_world)candidate) /\
    gateway_reference_parse_result python objects decimal_float detached io stable(Clight.globalenv prog)
      (plug_cont(gateway_dictionary_second_cont slots called_parameters)context)ledger held
      stream_block stream_offset initial(gateway_container_child_readonly slots readonly)child_before reading child child_after child_next.
Proof.
  intros CHILDREN FORMED GRAPHS MODE MODE_SUBSET LIMIT STACK ENTRIES PARENT KEY STREAM DEPTH INDEX STRING_KEY POSITIVE INPUT RUN NONNULL.
  destruct(gateway_reference_actual_dictionary_second backend python objects decimal_float detached io stable thread_errno heap_allocation
    runtime reference_threads context older ledger held parent_ticket parent parent_offset key_ticket key key_offset slots parameters depth index status size stream_block stream_offset
    initial readonly original before world events value after next STACK ENTRIES PARENT KEY STREAM DEPTH INDEX STRING_KEY POSITIVE INPUT RUN NONNULL)
    as(called_parameters &prefix &reading &suffix &child_before &child_world &child &child_after &child_next &EVENTS &QUIET &SHORT &
      CALLED_PARENT &CALLED_KEY &CALLED_STREAM &CALLED_DEPTH &CALLED_INDEX &PREFIX &CHILD_RUN &CHILD_NONNULL &REST &CALLED &CHILD_STACK &CHILD_BOUND &CHILD_CONTEXT &CHILD_NATIVE).
  pose proof CALLED as[COUNTED[SCOPE NATIVE]].
  assert(CHILD_MODE:gateway_unicode_strict_mode child_before(Vptr mode_symbol Ptrofs.zero)).
  { eapply gateway_value_context_current_mode;[exact(proj1(proj1(proj1 COUNTED)))|exact MODE|exact MODE_SUBSET]. }
  assert(PARSED:gateway_reference_parse_result python objects decimal_float detached io stable(Clight.globalenv prog)
    (plug_cont(gateway_dictionary_second_cont slots called_parameters)context)ledger held
    stream_block stream_offset initial(gateway_container_child_readonly slots readonly)child_before reading child child_after child_next).
  { eapply(CHILDREN(plug_cont(gateway_dictionary_second_cont slots called_parameters)context)ledger held
      {|gateway_value_stream:=Vptr stream_block stream_offset;gateway_value_depth:=Int.sub depth Int.one|}
      stream_block stream_offset initial(gateway_container_child_readonly slots readonly)child_before child_before child_world reading child child_after child_next).
    - cbn;exact I.
    - exact FORMED.
    - exact CHILD_STACK.
    - exact SCOPE.
    - exact GRAPHS.
    - exact CHILD_MODE.
    - intros object position MODE_POSITION;left;apply MODE_SUBSET;exact MODE_POSITION.
    - reflexivity.
    - exact CHILD_CONTEXT.
    - exact CHILD_NATIVE.
    - exact CHILD_RUN.
    - exact CHILD_NONNULL.
    - lia. }
  exists called_parameters,prefix,reading,suffix,child_before,child_world,child,child_after,child_next.
  split;[exact EVENTS|]. split;[exact QUIET|]. split;[exact SHORT|]. split;[exact CALLED_PARENT|]. split;[exact CALLED_KEY|]. split;[exact CALLED_STREAM|].
  split;[exact CALLED_DEPTH|]. split;[exact CALLED_INDEX|]. split;[exact PREFIX|]. split;[exact CHILD_RUN|]. split;[exact CHILD_NONNULL|].
  split;[exact REST|]. split;[exact CALLED|]. split;[exact CHILD_STACK|]. split;[exact CHILD_BOUND|]. split;[exact CHILD_CONTEXT|]. split;assumption.
Qed.
