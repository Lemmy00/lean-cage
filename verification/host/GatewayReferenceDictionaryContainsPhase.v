(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The same key reaches the actual duplicate check; successful
   continuation requires absence in the same owned dictionary, preserving its snapshots. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Machine CallContexts.
From HostGateway Require Import GatewaySource GatewayImport GatewayMachine GatewayContexts GatewayPython GatewayObjects GatewayReferences
  GatewayObjectDiscipline GatewayObjectThreads GatewayValue GatewayValueEntry GatewayContainerLength GatewayContainerLoopSource
  GatewayContainerDictionarySource GatewayContainerABI GatewayDictionaryBindings GatewayDictionaryCallReceipts
  GatewayReferenceDictionaryObservers GatewayReferenceObserverContextRun GatewayReferenceDictionaryKeyPhase
  GatewayReferenceLedger GatewayReferenceThreads GatewayReferenceGraphCapture GatewayReferenceContainerContext
  GatewayReadonly GatewayPathEvents GatewayObjectEvents GatewayObjectRuns GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Theorem gateway_reference_actual_dictionary_contains_phase {World Event}(backend:gateway_backend World Event)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (reference_threads:gateway_reference_thread_contract backend(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (containers:gateway_container_runtime backend python objects)(abi:gateway_container_abi_runtime backend python objects)
    (projection:gateway_direct_io_projection backend io)
    ledger held parent_ticket parent parent_offset fields entries parent_initial key_ticket key key_offset key_wire key_initial characters
    slots parameters status stream_block stream_offset initial readonly original size before world events value after next:
  parameters!_container=Some(Vptr parent parent_offset)->parameters!_first=Some(Vptr key key_offset)->0<Int.signed status->
  gateway_object_values parent_initial(Vptr parent parent_offset)=Some(gateway_dict_object fields)->
  gateway_object_values key_initial(Vptr key key_offset)=Some(gateway_unicode_object characters)->
  gateway_reference_counted_context python objects decimal_float detached stable ledger
    (held++[gateway_reference_graph_capture parent_ticket(Vptr parent parent_offset)
      (LeanCage_Host_GatewayResponseCode_Value_object(gateway_wire_fields entries))parent_initial;
      gateway_reference_graph_capture key_ticket(Vptr key key_offset)key_wire key_initial])
    gateway_container_object slots stream_block stream_offset initial readonly original size before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Returnstate(Vint status)(gateway_dictionary_key_cont slots parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  exists called_parameters prefix suffix called called_world,
    events=prefix++suffix /\(forall descriptor,gateway_received_bytes io descriptor prefix=[]) /\
    called_parameters!_string_key=Some(Vint status) /\called_parameters!_container=parameters!_container /\
    called_parameters!_first=parameters!_first /\called_parameters!_stream=parameters!_stream /\
    called_parameters!_depth=parameters!_depth /\called_parameters!_index__1=parameters!_index__1 /\
    gateway_dictionary_lookup characters fields=None /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate(Vint status)(gateway_dictionary_key_cont slots parameters)before)world)prefix
      (gateway_live(Returnstate(Vint Int.zero)(gateway_dictionary_contains_cont slots called_parameters)called)called_world) /\
    gateway_reference_counted_context python objects decimal_float detached stable ledger
      (held++[gateway_reference_graph_capture parent_ticket(Vptr parent parent_offset)
        (LeanCage_Host_GatewayResponseCode_Value_object(gateway_wire_fields entries))parent_initial;
        gateway_reference_graph_capture key_ticket(Vptr key key_offset)key_wire key_initial])
      gateway_container_object slots stream_block stream_offset initial readonly original size called called_world /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate(Vint Int.zero)(gateway_dictionary_contains_cont slots called_parameters)called)called_world)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros PARENT KEY POSITIVE PARENT_LOOKUP KEY_LOOKUP INPUT RUN NONNULL.
  set(parent_capture:=gateway_reference_graph_capture parent_ticket(Vptr parent parent_offset)
    (LeanCage_Host_GatewayResponseCode_Value_object(gateway_wire_fields entries))parent_initial).
  set(key_capture:=gateway_reference_graph_capture key_ticket(Vptr key key_offset)key_wire key_initial).
  set(all_held:=held++[parent_capture;key_capture]).
  assert(PARENT_MEMBER:In parent_capture all_held)by(apply in_or_app;right;left;reflexivity).
  assert(KEY_MEMBER:In key_capture all_held)by(apply in_or_app;right;right;left;reflexivity).
  set(property:=gateway_reference_counted_context python objects decimal_float detached stable ledger all_held gateway_container_object slots
    stream_block stream_offset initial readonly original size).
  pose proof(gateway_reference_counted_context_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation
    runtime reference_threads ledger all_held gateway_container_object slots stream_block stream_offset initial readonly original size)as CLOSED.
  destruct gateway_actual_dictionary_contains_binding as(definition &DEFINITION &[symbol[SYMBOL FUNCTION]]&TYPE).
  destruct(gateway_actual_dictionary_contains_receipt backend(Clight.globalenv prog)property slots parameters
    parent parent_offset key key_offset status before world events value after next symbol definition DEFINITION CLOSED
    ltac:(intros memory current returned changed following observed[COUNTED[SCOPE NATIVE]]OPERATION;
      eapply gateway_reference_dictionary_contains_integer;[exact abi|eapply GatewayContainerMemory.gateway_container_counted_side;exact COUNTED|
        exact SCOPE|exact PARENT_MEMBER|exact KEY_MEMBER|exact PARENT_LOOKUP|exact KEY_LOOKUP|exact OPERATION])
    PARENT KEY POSITIVE SYMBOL FUNCTION TYPE INPUT RUN NONNULL)
    as(called_parameters &source_prefix &checking &suffix &called_before &called_world_before &called &called_world &EVENTS &QUIET &STRING_KEY &
      CALLED_PARENT &CALLED_KEY &STREAM &DEPTH &INDEX &CALLED &PREFIX &CHECKING &REST).
  destruct(gateway_reference_actual_observer_context_run backend(Clight.globalenv prog)python objects decimal_float detached io stable thread_errno heap_allocation
    runtime reference_threads gateway_api_dict_contains definition[Vptr parent parent_offset;Vptr key key_offset](Vint Int.zero)
    (gateway_dictionary_lookup characters fields=None)ledger all_held gateway_container_object slots stream_block stream_offset initial readonly original size
    (gateway_value_environment slots)property called_before called_world_before checking called called_world DEFINITION CLOSED ltac:(intros;assumption)
    ltac:(intros memory current changed following observed[COUNTED[SCOPE NATIVE]]OPERATION;
      eapply gateway_reference_dictionary_contains_observed;[exact containers|eapply GatewayContainerMemory.gateway_container_counted_side;exact COUNTED|
        exact SCOPE|exact PARENT_MEMBER|exact KEY_MEMBER|exact PARENT_LOOKUP|exact KEY_LOOKUP|exact OPERATION])
    CALLED ltac:(eapply gateway_reference_counted_environment;exact CALLED)CHECKING)
    as[UNIQUE[CHECKED[ENV ORIGIN]]].
  exists called_parameters,(source_prefix++checking),suffix,called,called_world.
  split;[rewrite EVENTS,app_assoc;reflexivity|]. split.
  - intros descriptor;rewrite gateway_received_append,(gateway_quiet_received io descriptor source_prefix QUIET),
      (gateway_object_run_no_direct_receive backend(Clight.globalenv prog)io gateway_api_dict_contains definition
        [Vptr parent parent_offset;Vptr key key_offset]called_before called_world_before checking(Vint Int.zero)called called_world descriptor projection DEFINITION CHECKING);
      reflexivity.
  - split;[exact STRING_KEY|]. split;[exact CALLED_PARENT|]. split;[exact CALLED_KEY|]. split;[exact STREAM|].
    split;[exact DEPTH|]. split;[exact INDEX|]. split;[exact UNIQUE|]. split.
    + eapply gateway_steps_append;[exact PREFIX|].
      exact(gateway_plug_steps backend(Clight.globalenv prog)_ _ _ (gateway_dictionary_contains_cont slots called_parameters)ltac:(cbn;exact I)CHECKING).
    + split;assumption.
Qed.
