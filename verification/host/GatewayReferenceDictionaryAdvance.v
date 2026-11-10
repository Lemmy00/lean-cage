(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The same dictionary continuation releases its saved key and value
   owners independently, then advances the real loop without adding received bytes. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine CallContexts.
From HostGateway Require Import GatewaySource GatewayImport GatewayMachine GatewayContexts GatewayPython GatewayObjects GatewayReferences
  GatewayObjectDiscipline GatewayObjectThreads GatewayValue GatewayValueEntry GatewayValueEnvironment
  GatewayContainerLength GatewayContainerGuards GatewayContainerMemory GatewayContainerLoopSource GatewayContainerDictionarySource
  GatewayReferenceDictionaryResume GatewayDictionaryReleaseReceipts GatewaySourceSegments GatewaySourcePaths
  GatewayReferenceLedger GatewayReferenceAccounting GatewayReferencePlaces GatewayReferenceThreads GatewayReferenceNormalForm
  GatewayReferenceDictionaryNormalForm GatewayReferenceGraphCapture GatewayReferenceContainerScope GatewayReferenceContainerContext
  GatewayReferenceReleaseContextRun GatewayGraphSnapshots GatewayReadonly GatewayPathEvents GatewayObjectEvents GatewayObjectRuns
  GatewayReturnRuntime GatewayThreadRuntime GatewayStreamInterface GatewayFramedRuntime.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_reference_actual_dictionary_advance {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (reference_threads:gateway_reference_thread_contract backend(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (references:gateway_reference_runtime backend python objects)(projection:gateway_direct_io_projection backend io)
    context parent_ledger ledger held parent_ticket parent parent_offset fields entries parent_initial key_ticket key key_offset child_ticket child child_offset
    slots parameters index stream_block stream_offset initial readonly original size before world events value after next release_symbol definition:
  gateway_reference_ledger_well_formed ledger->
  gateway_reference_entries ledger=gateway_reference_entry child_ticket
    (gateway_reference_temporary(gateway_reference_depth context)_value__1)(Vptr child child_offset)::
    gateway_reference_entry key_ticket(gateway_reference_temporary(gateway_reference_depth context)_first)(Vptr key key_offset)::gateway_reference_entries parent_ledger->
  (forall captured,In captured held->gateway_held_ticket captured<>key_ticket /\gateway_held_ticket captured<>child_ticket)->
  parent_ticket<>key_ticket->parent_ticket<>child_ticket->
  gateway_object_values parent_initial(Vptr parent parent_offset)=Some(gateway_dict_object fields)->
  In(Vptr key key_offset)(gateway_dictionary_children fields)->In(Vptr child child_offset)(gateway_dictionary_children fields)->
  parameters!_first=Some(Vptr key key_offset)->parameters!_value__1=Some(Vptr child child_offset)->parameters!_index__1=Some(Vlong index)->
  gateway_reference_counted_context python objects decimal_float detached stable ledger
    (held++[gateway_reference_graph_capture parent_ticket(Vptr parent parent_offset)
      (LeanCage_Host_GatewayResponseCode_Value_object(gateway_wire_fields entries))parent_initial])
    gateway_container_object slots stream_block stream_offset initial readonly original size before world->
  gateway_object_api_definition gateway_api_decref=Some definition->
  Genv.find_symbol ge _Py_DecRef=Some release_symbol->Genv.find_funct_ptr ge release_symbol=Some definition->
  type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr)]tvoid cc_default->
  gateway_steps backend ge
    (gateway_live(Returnstate(Vint Int.zero)(gateway_dictionary_insert_cont slots parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists middle final release_parameters prefix suffix loop_memory loop_world,
    events=prefix++suffix /\(forall descriptor,gateway_received_bytes io descriptor prefix=[]) /\
    gateway_reference_ledger_well_formed final /\gateway_reference_entries final=gateway_reference_entries parent_ledger /\
    gateway_reference_next final=gateway_reference_next ledger /\
    gateway_reference_apply(gateway_reference_release(gateway_reference_temporary(gateway_reference_depth context)_first)(Vptr key key_offset))
      (gateway_reference_valid ledger)=gateway_reference_valid middle /\
    gateway_reference_apply(gateway_reference_release(gateway_reference_temporary(gateway_reference_depth context)_value__1)(Vptr child child_offset))
      (gateway_reference_valid middle)=gateway_reference_valid final /\
    release_parameters!_container=parameters!_container /\release_parameters!_stream=parameters!_stream /\
    release_parameters!_depth=parameters!_depth /\release_parameters!_index__1=Some(Vlong index) /\
    gateway_steps backend ge
      (gateway_live(State f_host_value gateway_container_loop gateway_container_loop_cont(gateway_value_environment slots)
        (gateway_dictionary_next_parameters index release_parameters)loop_memory)loop_world)suffix
      (gateway_live(Returnstate value Kstop after)next) /\
    gateway_reference_counted_context python objects decimal_float detached stable final
      (held++[gateway_reference_graph_capture parent_ticket(Vptr parent parent_offset)
        (LeanCage_Host_GatewayResponseCode_Value_object(gateway_wire_fields entries))parent_initial])
      gateway_container_object slots stream_block stream_offset initial readonly original size loop_memory loop_world.
Proof.
  intros FORMED ENTRIES OLD_TICKETS PARENT_KEY PARENT_CHILD LOOKUP KEY_MEMBER CHILD_MEMBER KEY CHILD INDEX INPUT DEFINITION SYMBOL FUNCTION TYPE RUN.
  set(parent_capture:=gateway_reference_graph_capture parent_ticket(Vptr parent parent_offset)
    (LeanCage_Host_GatewayResponseCode_Value_object(gateway_wire_fields entries))parent_initial).
  set(all_held:=held++[parent_capture]).
  assert(DESCENDANT:forall active current pointer,gateway_reference_scope python objects decimal_float active all_held current->
    In pointer(gateway_dictionary_children fields)->gateway_destructible(objects current)pointer).
  { intros active current pointer SCOPE MEMBER.
    pose proof(gateway_reference_capture_member _ _ _ _ _ _ _ SCOPE
      ltac:(unfold all_held;apply in_or_app;right;left;reflexivity))
      as[OWNER[PRIVATE[DESTROY[VALUE[INITIAL SNAPSHOT]]]]].
    assert(REACHED:gateway_object_reachable(objects current)(Vptr parent parent_offset)pointer).
    { eapply gateway_reachable_child;[constructor|rewrite SNAPSHOT by constructor;exact LOOKUP|exact MEMBER]. }
    intros object LATER;apply DESTROY;eapply gateway_reachable_trans;eassumption. }
  set(property:=gateway_reference_counted_context python objects decimal_float detached stable ledger all_held gateway_container_object slots
    stream_block stream_offset initial readonly original size).
  pose proof(gateway_reference_counted_context_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation
    runtime reference_threads ledger all_held gateway_container_object slots stream_block stream_offset initial readonly original size)as CLOSED.
  destruct(gateway_actual_dictionary_release_key_receipt backend ge property slots parameters Int.zero key key_offset before world events value after next
    release_symbol definition CLOSED KEY SYMBOL FUNCTION TYPE INPUT RUN)
    as(release_parameters &key_prefix &key_releasing &key_suffix &key_before &key_world &key_result &key_after &key_next &EVENTS &KEY_QUIET &STATUS &
      CALLED_PARENT &CALLED_KEY &CALLED_CHILD &CALLED_STREAM &CALLED_DEPTH &CALLED_INDEX &KEY_CALLED &KEY_PREFIX &KEY_RELEASE &KEY_REST).
  assert(KEY_OWNED:gateway_reference_owns ledger(gateway_reference_temporary(gateway_reference_depth context)_first)key_ticket(Vptr key key_offset)).
  { unfold gateway_reference_owns;rewrite ENTRIES;right;left;reflexivity. }
  destruct(gateway_reference_actual_release_context_run backend ge python objects decimal_float detached io stable thread_errno heap_allocation
    runtime reference_threads references gateway_container_object slots stream_block stream_offset initial readonly original size ledger
    (gateway_reference_temporary(gateway_reference_depth context)_first)key_ticket(Vptr key key_offset)all_held definition
    (gateway_value_environment slots)property key_before key_world key_releasing key_result key_after key_next FORMED DEFINITION CLOSED
    ltac:(intros memory current[COUNTED[SCOPE NATIVE]];
      exact(conj SCOPE(conj KEY_OWNED(conj(DESCENDANT ledger current(Vptr key key_offset)SCOPE KEY_MEMBER)(conj COUNTED NATIVE)))))
    ltac:(intros captured MEMBER;unfold all_held in MEMBER;apply in_app_or in MEMBER;destruct MEMBER as[OLD|[SAME|EMPTY]];
      [exact(proj1(OLD_TICKETS captured OLD))|subst captured;exact PARENT_KEY|contradiction])KEY_CALLED
    ltac:(destruct KEY_CALLED as[COUNTED OTHER];eapply gateway_value_active_environment;exact(proj1(proj1 COUNTED)))KEY_RELEASE)
    as(middle &key_operation_prefix &key_operation_suffix &key_called &key_called_world &key_changed &key_changed_world &key_observed &KEY_ACTION &MIDDLE_FORMED &MIDDLE_SCOPE &
      MIDDLE_ENV &MIDDLE_COUNTED &MIDDLE_NATIVE &KEY_OP_EVENTS &KEY_OPERATION &KEY_RETAINED).
  destruct(gateway_reference_dictionary_key_release context ledger middle(gateway_reference_entries parent_ledger)
    key_ticket(Vptr key key_offset)child_ticket(Vptr child child_offset)ENTRIES KEY_ACTION)as[MIDDLE_ENTRIES MIDDLE_NEXT].
  set(middle_property:=gateway_reference_counted_context python objects decimal_float detached stable middle all_held gateway_container_object slots
    stream_block stream_offset initial readonly original size).
  pose proof(gateway_reference_counted_context_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation
    runtime reference_threads middle all_held gateway_container_object slots stream_block stream_offset initial readonly original size)as MIDDLE_CLOSED.
  destruct(gateway_actual_dictionary_release_child_receipt backend ge middle_property slots release_parameters key_result child child_offset
    key_after key_next key_suffix value after next release_symbol definition MIDDLE_CLOSED
    ltac:(rewrite CALLED_CHILD;exact CHILD)SYMBOL FUNCTION TYPE(conj MIDDLE_COUNTED(conj MIDDLE_SCOPE MIDDLE_NATIVE))KEY_REST)
    as(child_prefix &child_releasing &child_suffix &child_before &child_world &child_result &child_after &child_next &CHILD_EVENTS &CHILD_QUIET &CHILD_CALLED &
      CHILD_PREFIX &CHILD_RELEASE &CHILD_REST).
  assert(CHILD_OWNED:gateway_reference_owns middle(gateway_reference_temporary(gateway_reference_depth context)_value__1)child_ticket(Vptr child child_offset)).
  { unfold gateway_reference_owns;rewrite MIDDLE_ENTRIES;left;reflexivity. }
  destruct(gateway_reference_actual_release_context_run backend ge python objects decimal_float detached io stable thread_errno heap_allocation
    runtime reference_threads references gateway_container_object slots stream_block stream_offset initial readonly original size middle
    (gateway_reference_temporary(gateway_reference_depth context)_value__1)child_ticket(Vptr child child_offset)all_held definition
    (gateway_value_environment slots)middle_property child_before child_world child_releasing child_result child_after child_next MIDDLE_FORMED DEFINITION MIDDLE_CLOSED
    ltac:(intros memory current[COUNTED[SCOPE NATIVE]];
      exact(conj SCOPE(conj CHILD_OWNED(conj(DESCENDANT middle current(Vptr child child_offset)SCOPE CHILD_MEMBER)(conj COUNTED NATIVE)))))
    ltac:(intros captured MEMBER;unfold all_held in MEMBER;apply in_app_or in MEMBER;destruct MEMBER as[OLD|[SAME|EMPTY]];
      [exact(proj2(OLD_TICKETS captured OLD))|subst captured;exact PARENT_CHILD|contradiction])CHILD_CALLED
    ltac:(destruct CHILD_CALLED as[COUNTED OTHER];eapply gateway_value_active_environment;exact(proj1(proj1 COUNTED)))CHILD_RELEASE)
    as(final &child_operation_prefix &child_operation_suffix &child_called &child_called_world &child_changed &child_changed_world &child_observed &CHILD_ACTION &FINAL_FORMED &FINAL_SCOPE &
      FINAL_ENV &FINAL_COUNTED &FINAL_NATIVE &CHILD_OP_EVENTS &CHILD_OPERATION &CHILD_RETAINED).
  destruct(gateway_reference_head_release middle final(gateway_reference_entries parent_ledger)child_ticket
    (gateway_reference_temporary(gateway_reference_depth context)_value__1)(Vptr child child_offset)MIDDLE_ENTRIES CHILD_ACTION)
    as[FINAL_ENTRIES FINAL_NEXT].
  set(final_property:=gateway_reference_counted_context python objects decimal_float detached stable final all_held gateway_container_object slots
    stream_block stream_offset initial readonly original size).
  pose proof(gateway_reference_counted_context_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation
    runtime reference_threads final all_held gateway_container_object slots stream_block stream_offset initial readonly original size)as FINAL_CLOSED.
  pose proof(gateway_dictionary_next_source_segment backend ge final_property slots release_parameters child_result index child_after
    FINAL_CLOSED STATUS ltac:(rewrite CALLED_INDEX;exact INDEX))as SEGMENT.
  destruct(gateway_source_segment_cut backend ge _ _ _ _ SEGMENT child_after child_next child_suffix value after next
    (conj FINAL_COUNTED(conj FINAL_SCOPE FINAL_NATIVE))CHILD_REST)
    as(advancing &suffix &loop_memory &loop_world &ADVANCE_EVENTS &ADVANCE_QUIET &ADVANCE &LOOP_READY &LOOP_RUN).
  exists middle,final,release_parameters,(key_prefix++key_releasing++child_prefix++child_releasing++advancing),suffix,loop_memory,loop_world.
  split;[rewrite EVENTS,CHILD_EVENTS,ADVANCE_EVENTS;repeat rewrite app_assoc;reflexivity|]. split.
  - intros descriptor;rewrite !gateway_received_append,(gateway_quiet_received io descriptor key_prefix KEY_QUIET),
      (gateway_object_run_no_direct_receive backend ge io gateway_api_decref definition[Vptr key key_offset]
        key_before key_world key_releasing key_result key_after key_next descriptor projection DEFINITION KEY_RELEASE),
      (gateway_quiet_received io descriptor child_prefix CHILD_QUIET),
      (gateway_object_run_no_direct_receive backend ge io gateway_api_decref definition[Vptr child child_offset]
        child_before child_world child_releasing child_result child_after child_next descriptor projection DEFINITION CHILD_RELEASE),
      (gateway_quiet_received io descriptor advancing ADVANCE_QUIET);reflexivity.
  - split;[exact FINAL_FORMED|]. split;[exact FINAL_ENTRIES|]. split;[rewrite FINAL_NEXT;exact MIDDLE_NEXT|].
    split;[exact KEY_ACTION|]. split;[exact CHILD_ACTION|]. split;[exact CALLED_PARENT|]. split;[exact CALLED_STREAM|].
    split;[exact CALLED_DEPTH|]. split;[rewrite CALLED_INDEX;exact INDEX|]. split;assumption.
Qed.
