(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The first recursive result reaches the real key check and moves
   into the actual saved key place, retaining the same parent, stream and references. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Ctypesdefs Clight.
Require Import Machine CallContexts.
From HostGateway Require Import GatewaySource GatewayImport GatewayMachine GatewayContexts GatewayPython GatewayObjects GatewayReferences
  GatewayObjectDiscipline GatewayObjectThreads GatewayObjectInstances GatewayValue GatewayValueEntry GatewayValueEnvironment
  GatewayContainerLength GatewayContainerGuards GatewayContainerMemory GatewayContainerLoopSource GatewayContainerDictionarySource
  GatewayDictionaryBindings GatewayDictionaryCallReceipts GatewayReferenceDictionaryObservers GatewayReferenceObserverContextRun
  GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting GatewayReferenceMoves GatewayReferenceNormalForm
  GatewayReferenceStackBound GatewayReferenceLoopLedger GatewayReferenceDictionaryLedger GatewayReferenceChildOwnership
  GatewayReferenceGraphCapture GatewayReferenceContainerScope GatewayReferenceContainerContext GatewayReferenceThreads GatewayReferenceEmptyContainer
  GatewayReadonly GatewayPathEvents GatewayReturnRuntime GatewayObjectEvents GatewayObjectRuns GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Lemma gateway_reference_counted_environment {World}python objects decimal_float detached stable ledger held container slots
    stream_block stream_offset initial readonly original size memory world:
  @gateway_reference_counted_context World python objects decimal_float detached stable ledger held container slots
    stream_block stream_offset initial readonly original size memory world->
  gateway_return_environment(fun current candidate=>gateway_native_private(python current)candidate)
    (gateway_python_discipline python objects detached)None(gateway_value_environment slots)memory world.
Proof.
  intros[COUNTED[SCOPE NATIVE]];split.
  - eapply gateway_container_counted_side;exact COUNTED.
  - eapply gateway_value_active_environment;exact(proj1(proj1 COUNTED)).
Qed.

Lemma gateway_reference_counted_capture_pointer {World}python objects decimal_float detached stable ledger held container slots
    stream_block stream_offset initial readonly original size memory world ticket object offset wire snapshot:
  @gateway_reference_counted_context World python objects decimal_float detached stable ledger held container slots
    stream_block stream_offset initial readonly original size memory world->
  In(gateway_reference_graph_capture ticket(Vptr object offset)wire snapshot)held->
  Mem.weak_valid_pointer memory object(Ptrofs.unsigned offset)=true.
Proof.
  intros[COUNTED[SCOPE NATIVE]]MEMBER.
  destruct(gateway_reference_capture_member _ _ _ _ _ _ _ SCOPE MEMBER)as[[owner OWNED]REST].
  destruct(gateway_reference_owned_pointer python objects ledger owner ticket(Vptr object offset)memory world
    ltac:(eapply gateway_container_counted_side;exact COUNTED)(proj1 SCOPE)OWNED)as(actual &actual_offset &SAME &VALID).
  inversion SAME;subst;exact VALID.
Qed.

Theorem gateway_reference_actual_dictionary_key_phase {World Event}(backend:gateway_backend World Event)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (reference_threads:gateway_reference_thread_contract backend(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (instances:gateway_instance_runtime backend(Clight.globalenv prog)python objects(fun _ _ _=>Logic.False))
    (projection:gateway_direct_io_projection backend io)
    context older parent_ledger key_ledger held parent_ticket parent parent_offset entries parent_initial
    key_ticket key key_offset key_wire key_initial slots parameters stream_block stream_offset initial readonly original size
    before world events value after next:
  gateway_reference_stack_bound context older->gateway_reference_ledger_well_formed key_ledger->
  gateway_reference_loop_entries context older parent_ledger parent_ticket(Vptr parent parent_offset)->
  gateway_reference_result_entries(plug_cont(gateway_container_first_cont slots parameters)context)parent_ledger key_ledger
    key_ticket(Vptr key key_offset)->
  gateway_reference_counted_context python objects decimal_float detached stable key_ledger
    (held++[gateway_reference_graph_capture parent_ticket(Vptr parent parent_offset)
      (LeanCage_Host_GatewayResponseCode_Value_object(gateway_wire_fields entries))parent_initial;
      gateway_reference_graph_capture key_ticket(Vptr key key_offset)key_wire key_initial])
    gateway_container_object slots stream_block stream_offset initial readonly original size before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Returnstate(Vptr key key_offset)(gateway_container_first_cont slots parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  exists adopted called_parameters status characters prefix suffix called called_world,
    events=prefix++suffix /\(forall descriptor,gateway_received_bytes io descriptor prefix=[]) /\
    gateway_reference_ledger_well_formed adopted /\
    gateway_reference_dictionary_entries context older adopted parent_ticket(Vptr parent parent_offset)key_ticket(Vptr key key_offset) /\
    gateway_reference_next adopted=gateway_reference_next key_ledger /\
    called_parameters!_first=Some(Vptr key key_offset) /\called_parameters!_container=parameters!_container /\
    called_parameters!_stream=parameters!_stream /\called_parameters!_depth=parameters!_depth /\
    called_parameters!_index__1=parameters!_index__1 /\0<Int.signed status /\
    gateway_object_values key_initial(Vptr key key_offset)=Some(gateway_unicode_object characters) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate(Vptr key key_offset)(gateway_container_first_cont slots parameters)before)world)prefix
      (gateway_live(Returnstate(Vint status)(gateway_dictionary_key_cont slots called_parameters)called)called_world) /\
    gateway_reference_counted_context python objects decimal_float detached stable adopted
      (held++[gateway_reference_graph_capture parent_ticket(Vptr parent parent_offset)
        (LeanCage_Host_GatewayResponseCode_Value_object(gateway_wire_fields entries))parent_initial;
        gateway_reference_graph_capture key_ticket(Vptr key key_offset)key_wire key_initial])
      gateway_container_object slots stream_block stream_offset initial readonly original size called called_world /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(Returnstate(Vint status)(gateway_dictionary_key_cont slots called_parameters)called)called_world)suffix
      (gateway_live(Returnstate value Kstop after)next).
Proof.
  intros STACK FORMED PARENT_ENTRIES KEY_ENTRIES INPUT RUN NONNULL.
  set(parent_capture:=gateway_reference_graph_capture parent_ticket(Vptr parent parent_offset)
    (LeanCage_Host_GatewayResponseCode_Value_object(gateway_wire_fields entries))parent_initial).
  set(key_capture:=gateway_reference_graph_capture key_ticket(Vptr key key_offset)key_wire key_initial).
  set(all_held:=held++[parent_capture;key_capture]).
  assert(KEY_MEMBER:In key_capture all_held)by(apply in_or_app;right;right;left;reflexivity).
  set(property:=gateway_reference_counted_context python objects decimal_float detached stable key_ledger all_held gateway_container_object slots
    stream_block stream_offset initial readonly original size).
  pose proof(gateway_reference_counted_context_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation
    runtime reference_threads key_ledger all_held gateway_container_object slots stream_block stream_offset initial readonly original size)as CLOSED.
  destruct gateway_actual_dictionary_key_binding as(definition &DEFINITION &[symbol[SYMBOL FUNCTION]]&TYPE).
  destruct gateway_actual_dictionary_unicode_binding as[unicode[UNICODE CLASS]].
  destruct(gateway_actual_dictionary_key_receipt backend(Clight.globalenv prog)property slots parameters key key_offset before world events value after next
    symbol definition unicode DEFINITION CLOSED
    ltac:(intros memory current returned changed following observed[COUNTED[SCOPE NATIVE]]OPERATION;
      eapply gateway_reference_dictionary_key_integer;[exact instances|eapply gateway_container_counted_side;exact COUNTED|
        exact SCOPE|exact KEY_MEMBER|exact CLASS|exact OPERATION])
    ltac:(intros memory current READY;eapply gateway_reference_counted_capture_pointer;[exact READY|exact KEY_MEMBER])
    ltac:(intros memory current[COUNTED REST];exact(proj2(proj1 COUNTED)))
    SYMBOL FUNCTION UNICODE TYPE INPUT RUN NONNULL)
    as(called_parameters &source_prefix &checking &suffix &called_before &called_world_before &called &called_world &status &EVENTS &QUIET &FIRST &PARENT &
      STREAM &DEPTH &INDEX &CALLED &POSITIVE &PREFIX &CHECKING &REST).
  pose proof CALLED as[COUNTED[SCOPE NATIVE]].
  destruct(gateway_reference_adopt_child python objects decimal_float(plug_cont(gateway_container_first_cont slots parameters)context)
    parent_ledger key_ledger key_ticket(Vptr key key_offset)all_held called_world_before
    (gateway_reference_temporary(gateway_reference_depth context)_first)FORMED KEY_ENTRIES ltac:(discriminate)
    ltac:(eapply gateway_reference_loop_free;[exact STACK|exact PARENT_ENTRIES|discriminate])SCOPE)
    as(adopted &MOVE &WELL &ENTRIES &COUNTER &KEY_OWNED &ADOPTED_SCOPE).
  set(adopted_property:=gateway_reference_counted_context python objects decimal_float detached stable adopted all_held gateway_container_object slots
    stream_block stream_offset initial readonly original size).
  pose proof(gateway_reference_counted_context_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation
    runtime reference_threads adopted all_held gateway_container_object slots stream_block stream_offset initial readonly original size)as ADOPTED_CLOSED.
  assert(ADOPTED:adopted_property called_before called_world_before)by(exact(conj COUNTED(conj ADOPTED_SCOPE NATIVE))).
  destruct(gateway_reference_actual_observer_context_run backend(Clight.globalenv prog)python objects decimal_float detached io stable thread_errno heap_allocation
    runtime reference_threads gateway_api_is_instance definition[Vptr key key_offset;Vptr unicode Ptrofs.zero](Vint status)
    (exists characters,gateway_object_values key_initial(Vptr key key_offset)=Some(gateway_unicode_object characters))
    adopted all_held gateway_container_object slots stream_block stream_offset initial readonly original size(gateway_value_environment slots)
    adopted_property called_before called_world_before checking called called_world DEFINITION ADOPTED_CLOSED ltac:(intros;assumption)
    ltac:(intros memory current changed following observed[CURRENT[SCOPE_NOW NATIVE_NOW]]OPERATION;
      eapply gateway_reference_dictionary_key_observed;[exact instances|eapply gateway_container_counted_side;exact CURRENT|
        exact SCOPE_NOW|exact KEY_MEMBER|exact CLASS|exact POSITIVE|exact OPERATION])ADOPTED
    ltac:(eapply gateway_reference_counted_environment;exact ADOPTED)CHECKING)
    as[[characters KEY_LOOKUP][CHECKED[ENV ORIGIN]]].
  exists adopted,called_parameters,status,characters,(source_prefix++checking),suffix,called,called_world.
  split;[rewrite EVENTS,app_assoc;reflexivity|]. split.
  - intros descriptor;rewrite gateway_received_append,(gateway_quiet_received io descriptor source_prefix QUIET),
      (gateway_object_run_no_direct_receive backend(Clight.globalenv prog)io gateway_api_is_instance definition
        [Vptr key key_offset;Vptr unicode Ptrofs.zero]called_before called_world_before checking(Vint status)called called_world descriptor projection DEFINITION CHECKING);
      reflexivity.
  - split;[exact WELL|]. split.
    + unfold gateway_reference_dictionary_entries;rewrite ENTRIES,PARENT_ENTRIES;reflexivity.
    + split;[exact COUNTER|]. split;[exact FIRST|]. split;[exact PARENT|]. split;[exact STREAM|].
      split;[exact DEPTH|]. split;[exact INDEX|]. split;[exact POSITIVE|]. split;[exact KEY_LOOKUP|]. split.
      * eapply gateway_steps_append;[exact PREFIX|].
        exact(gateway_plug_steps backend(Clight.globalenv prog)_ _ _ (gateway_dictionary_key_cont slots called_parameters)ltac:(cbn;exact I)CHECKING).
      * split;assumption.
Qed.
