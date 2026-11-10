(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The second recursive receipt composes with real dictionary insertion
   and selected releases, returning the next source loop frontier. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Machine CallContexts.
From HostGateway Require Import GatewaySource GatewayImport GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayObjectDiscipline GatewayObjectThreads
  GatewayValue GatewayValueEntry GatewayValueContext GatewayValueStack GatewayContainerLength GatewayContainerGuards GatewayContainerMemory
  GatewayContainerLoopSource GatewayContainerDictionarySource GatewayReferenceDictionaryResume GatewayContainerChildContext GatewayContainerABI GatewayArrayBindings
  GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting GatewayReferenceThreads GatewayReferenceStackBound GatewayReferenceLoopLedger GatewayReferenceDictionaryLedger
  GatewayReferenceNormalForm GatewayReferenceDecoded GatewayReferenceParseResult GatewayReferenceValueProperties GatewayReferenceAncestors GatewayReferenceSnapshotInputs
  GatewayReferenceGraphCapture GatewayReferenceContainerScope GatewayReferenceContainerContext GatewayReferenceEmptyContainer
  GatewayReferenceDictionaryStep GatewayReferenceDictionaryAdvance GatewayReferenceDictionaryTarget GatewayDictionaryBindings GatewayReferenceMoves GatewayContainerEncoding GatewayThreadRuntime GatewayStreamInterface GatewayObjectEvents GatewayObjectRuns GatewayPathEvents.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_reference_actual_dictionary_second_resume {World Event}(backend:gateway_backend World Event)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (reference_threads:gateway_reference_thread_contract backend(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (containers:gateway_container_runtime backend python objects)(abi:gateway_container_abi_runtime backend python objects)
    (references:gateway_reference_runtime backend python objects)(projection:gateway_direct_io_projection backend io)
    context older loop_ledger ledger held parent_ticket parent parent_offset fields entries parent_initial
    key_ticket key key_offset key_value key_initial characters slots parameters depth index size
    stream_block stream_offset initial readonly original child_before child_world reading child child_after child_next
    events value after next:
  gateway_reference_stack_bound context older->gateway_reference_ledger_well_formed ledger->
  gateway_reference_loop_entries context older loop_ledger parent_ticket(Vptr parent parent_offset)->
  gateway_reference_dictionary_entries context older ledger parent_ticket(Vptr parent parent_offset)key_ticket(Vptr key key_offset)->
  (gateway_reference_next loop_ledger<=key_ticket)%nat->
  (forall captured,In captured held->gateway_held_ticket captured<>key_ticket)->parent_ticket<>key_ticket->
  gateway_reference_graphs_only held->gateway_reference_snapshots_avoid held(Vptr parent parent_offset)->
  gateway_object_values parent_initial(Vptr parent parent_offset)=Some(gateway_dict_object fields)->
  gateway_dictionary_heap decimal_float parent_initial fields entries->
  (forall pointer,In pointer(gateway_dictionary_children fields)->~gateway_object_reachable parent_initial pointer(Vptr parent parent_offset))->
  (forall pointer,gateway_reference_mutable_target held pointer->~gateway_object_reachable parent_initial(Vptr parent parent_offset)pointer)->
  gateway_object_values key_initial(Vptr key key_offset)=Some(gateway_unicode_object characters)->
  gateway_dictionary_lookup characters fields=None->
  ~gateway_object_reachable key_initial(Vptr key key_offset)(Vptr parent parent_offset)->
  (forall pointer,gateway_reference_mutable_target held pointer->~gateway_object_reachable key_initial(Vptr key key_offset)pointer)->
  parameters!_container=Some(Vptr parent parent_offset)->parameters!_first=Some(Vptr key key_offset)->parameters!_stream=Some(Vptr stream_block stream_offset)->
  parameters!_depth=Some(Vint depth)->parameters!_index__1=Some(Vlong index)->
  gateway_reference_counted_context python objects decimal_float detached stable ledger
    (held++[gateway_reference_graph_capture parent_ticket(Vptr parent parent_offset)
      (LeanCage_Host_GatewayResponseCode_Value_object(gateway_wire_fields entries))parent_initial;gateway_reference_graph_capture key_ticket(Vptr key key_offset)key_value key_initial])
    gateway_container_object slots stream_block stream_offset initial readonly original size child_before child_world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_value)[Vptr stream_block stream_offset;Vint(Int.sub depth Int.one)]Kstop child_before)child_world)reading
    (gateway_live(Returnstate child Kstop child_after)child_next)->
  gateway_reference_parse_result python objects decimal_float detached io stable(Clight.globalenv prog)
    (plug_cont(gateway_dictionary_second_cont slots parameters)context)ledger
    (held++[gateway_reference_graph_capture parent_ticket(Vptr parent parent_offset)
      (LeanCage_Host_GatewayResponseCode_Value_object(gateway_wire_fields entries))parent_initial;gateway_reference_graph_capture key_ticket(Vptr key key_offset)key_value key_initial])
    stream_block stream_offset initial(gateway_container_child_readonly slots readonly)child_before reading child child_after child_next->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Returnstate child(gateway_dictionary_second_cont slots parameters)child_after)child_next)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  exists final final_stream child_value child_ticket object offset loop_parameters prefix suffix loop_memory loop_world parent_snapshot,
    events=prefix++suffix /\
    (forall descriptor,gateway_received_bytes io descriptor prefix=[]) /\
    gateway_response_frame(LeanCage_Host_GatewayResponseCode_Subject_value child_value)
      (gateway_received_bytes io(stream_descriptor initial)reading) /\
    (gateway_reference_next ledger<=child_ticket)%nat /\
    child=Vptr object offset /\gateway_reference_ledger_well_formed final /\
    gateway_reference_loop_entries context older final parent_ticket(Vptr parent parent_offset) /\
    loop_parameters!_container=Some(Vptr parent parent_offset) /\loop_parameters!_stream=Some(Vptr stream_block stream_offset) /\
    loop_parameters!_depth=Some(Vint depth) /\loop_parameters!_index__1=Some(Vlong(Int64.add index Int64.one)) /\
    gateway_steps backend(Clight.globalenv prog)
      (gateway_live(State f_host_value gateway_container_loop gateway_container_loop_cont(gateway_value_environment slots)loop_parameters loop_memory)loop_world)suffix
      (gateway_live(Returnstate value Kstop after)next) /\
    gateway_reference_counted_context python objects decimal_float detached stable final
      (held++[gateway_reference_graph_capture parent_ticket(Vptr parent parent_offset)
        (LeanCage_Host_GatewayResponseCode_Value_object(gateway_wire_fields(entries++[(key_value,child_value)])))parent_snapshot])
      gateway_container_object slots stream_block stream_offset final_stream readonly original size loop_memory loop_world /\
    stream_descriptor final_stream=stream_descriptor initial /\
    gateway_object_values parent_snapshot(Vptr parent parent_offset)=Some(gateway_dict_object(fields++[{|gateway_dictionary_key:=Vptr key key_offset;gateway_dictionary_text:=characters;gateway_dictionary_value:=Vptr object offset|}])) /\
    gateway_dictionary_heap decimal_float parent_snapshot(fields++[{|gateway_dictionary_key:=Vptr key key_offset;gateway_dictionary_text:=characters;gateway_dictionary_value:=Vptr object offset|}])(entries++[(key_value,child_value)]) /\
    (forall pointer,In pointer(gateway_dictionary_children fields++[Vptr key key_offset;Vptr object offset])->~gateway_object_reachable parent_snapshot pointer(Vptr parent parent_offset)) /\
    (forall pointer,gateway_reference_mutable_target held pointer->~gateway_object_reachable parent_snapshot(Vptr parent parent_offset)pointer).
Proof.
  intros STACK FORMED ENTRIES DICT_ENTRIES KEY_FRESH OLD_KEY_TICKETS PARENT_KEY GRAPHS OUTSIDE LOOKUP FIELDS ACYCLIC EXCLUDED KEY_LOOKUP UNIQUE KEY_OUTSIDE KEY_EXCLUDED
    PARENT KEY STREAM DEPTH INDEX INPUT CHILD_EXECUTION PARSED RUN NONNULL.
  set(parent_capture:=gateway_reference_graph_capture parent_ticket(Vptr parent parent_offset)
    (LeanCage_Host_GatewayResponseCode_Value_object(gateway_wire_fields entries))parent_initial).
  set(key_capture:=gateway_reference_graph_capture key_ticket(Vptr key key_offset)key_value key_initial).
  destruct PARSED as(child_ledger &final_stream &child_value &child_ticket &DECODED &CHILD_CONTEXT &CHILD_NATIVE &DESCRIPTOR &FRAMED).
  pose proof DECODED as[CHILD_FORMED CHILD_ENTRIES CHILD_FRESH CHILD_OWNER CHILD_BOUND CHILD_SCOPE CHILD_VALUE CHILD_AVOIDS].
  pose proof INPUT as[COUNTED[SCOPE NATIVE]].
  destruct(gateway_container_child_return(fun current candidate=>gateway_native_private(python current)candidate)stable
    (gateway_python_discipline python objects detached)gateway_container_object slots stream_block stream_offset initial final_stream readonly original size
    child_before child_world child_after child_next COUNTED CHILD_CONTEXT CHILD_NATIVE)as[RETURN_COUNTED RETURN_NATIVE].
  destruct(gateway_reference_owned_pointer python objects child_ledger _ _ child child_after child_next
    (proj1 CHILD_CONTEXT)(proj1 CHILD_SCOPE)CHILD_OWNER)as(object &offset &CHILD_POINTER &VALID);subst child.
  assert(CHILD_OUTSIDE:~gateway_object_reachable(objects child_next)(Vptr object offset)(Vptr parent parent_offset)).
  { apply(proj1(gateway_reference_avoids_targets _ _ _)CHILD_AVOIDS).
    eapply gateway_reference_target_sublist with(selected:=held++[parent_capture]).
    - intros captured MEMBER;apply in_app_or in MEMBER;apply in_or_app;destruct MEMBER as[OLD|[SAME|EMPTY]];
        [left;exact OLD|right;left;exact SAME|contradiction].
    - apply gateway_reference_dictionary_target with(fields:=fields);exact LOOKUP. }
  assert(ALL_SCOPE:gateway_reference_scope python objects decimal_float child_ledger
    (held++[parent_capture;key_capture;gateway_reference_graph_capture child_ticket(Vptr object offset)child_value(objects child_next)])child_next).
  { rewrite<-app_assoc in CHILD_SCOPE;exact CHILD_SCOPE. }
  assert(CHILD_INPUT:gateway_reference_counted_context python objects decimal_float detached stable child_ledger
    (held++[parent_capture;key_capture;gateway_reference_graph_capture child_ticket(Vptr object offset)child_value(objects child_next)])
    gateway_container_object slots stream_block stream_offset final_stream readonly original size child_after child_next)
    by(exact(conj RETURN_COUNTED(conj ALL_SCOPE RETURN_NATIVE))).
  destruct gateway_actual_dictionary_insert_binding as(insert_definition &INSERT_DEFINITION &[insert_symbol[INSERT_SYMBOL INSERT_FUNCTION]]&INSERT_TYPE).
  destruct gateway_actual_value_release_binding as(release_definition &RELEASE_DEFINITION &[release_symbol[RELEASE_SYMBOL RELEASE_FUNCTION]]&RELEASE_TYPE).
  destruct(gateway_reference_actual_dictionary_step backend(Clight.globalenv prog)python objects decimal_float detached io stable thread_errno heap_allocation
    runtime reference_threads containers abi(gateway_reference_mutable_target held)context older ledger child_ledger held parent_ticket parent parent_offset
    fields entries parent_initial key_ticket key key_offset characters key_value key_initial child_ticket object offset child_value(objects child_next)
    slots parameters stream_block stream_offset final_stream readonly original size child_after child_next events value after next
    insert_symbol insert_definition release_symbol release_definition STACK CHILD_FORMED DICT_ENTRIES CHILD_ENTRIES GRAPHS OUTSIDE LOOKUP FIELDS ACYCLIC
    KEY_LOOKUP UNIQUE KEY_OUTSIDE CHILD_OUTSIDE
    ltac:(intros pointer FORBIDDEN;split;[apply EXCLUDED;exact FORBIDDEN|split;[apply KEY_EXCLUDED;exact FORBIDDEN|
      apply(proj1(gateway_reference_avoids_targets _ _ _)CHILD_AVOIDS);eapply gateway_reference_target_sublist;
        [intros captured MEMBER;apply in_or_app;left;exact MEMBER|exact FORBIDDEN]]])PARENT KEY CHILD_INPUT
    INSERT_DEFINITION INSERT_SYMBOL INSERT_FUNCTION INSERT_TYPE RELEASE_SYMBOL RELEASE_FUNCTION RELEASE_TYPE RUN NONNULL)
    as(adopted &called_parameters &source_prefix &inserting &rest &insert_before &insert_world &insert_after &insert_next &EVENTS &PREFIX_QUIET &WELL &
      ADOPTED_ENTRIES &NEXT_COUNTER &MOVE &CALLED_PARENT &CALLED_KEY &CALLED_CHILD &CALLED_STREAM &CALLED_DEPTH &CALLED_INDEX &TO_INSERT &INSERTING &REST &UPDATED &
      UPDATED_LOOKUP &UPDATED_FIELDS &UPDATED_ACYCLIC &UPDATED_EXCLUDED).
  assert(OLD_TICKETS:forall captured,In captured held->gateway_held_ticket captured<>key_ticket /\gateway_held_ticket captured<>child_ticket).
  { intros captured MEMBER;split;[apply OLD_KEY_TICKETS;exact MEMBER|]. intro SAME.
    pose proof(gateway_reference_scope_ticket_bound python objects decimal_float ledger(held++[parent_capture;key_capture])child_world captured
      FORMED SCOPE ltac:(apply in_or_app;left;exact MEMBER))as BELOW;lia. }
  assert(PARENT_CHILD:parent_ticket<>child_ticket).
  { pose proof(gateway_reference_scope_ticket_bound python objects decimal_float ledger(held++[parent_capture;key_capture])child_world parent_capture
      FORMED SCOPE ltac:(apply in_or_app;right;left;reflexivity))as BELOW;cbn in BELOW;lia. }
  destruct(gateway_reference_actual_dictionary_advance backend(Clight.globalenv prog)python objects decimal_float detached io stable thread_errno heap_allocation
    runtime reference_threads references projection context loop_ledger adopted held parent_ticket parent parent_offset
    (fields++[{|gateway_dictionary_key:=Vptr key key_offset;gateway_dictionary_text:=characters;gateway_dictionary_value:=Vptr object offset|}])
    (entries++[(key_value,child_value)])(objects insert_next)key_ticket key key_offset child_ticket object offset slots called_parameters index
    stream_block stream_offset final_stream readonly original size insert_after insert_next rest value after next release_symbol release_definition WELL
    ltac:(rewrite ADOPTED_ENTRIES,DICT_ENTRIES;rewrite ENTRIES;reflexivity)OLD_TICKETS PARENT_KEY PARENT_CHILD UPDATED_LOOKUP
    ltac:(unfold gateway_dictionary_children;rewrite flat_map_app;apply in_or_app;right;left;reflexivity)
    ltac:(unfold gateway_dictionary_children;rewrite flat_map_app;apply in_or_app;right;right;left;reflexivity)
    CALLED_KEY CALLED_CHILD ltac:(rewrite CALLED_INDEX;exact INDEX)UPDATED RELEASE_DEFINITION RELEASE_SYMBOL RELEASE_FUNCTION RELEASE_TYPE REST)
    as(middle &final &release_parameters &release_prefix &suffix &loop_memory &loop_world &REST_EVENTS &RELEASE_EMPTY &FINAL_WELL &FINAL_ENTRIES &FINAL_NEXT &
      KEY_RELEASE &CHILD_RELEASE &RELEASE_PARENT &RELEASE_STREAM &RELEASE_DEPTH &RELEASE_INDEX &LOOP_RUN &LOOP_READY).
  exists final,final_stream,child_value,child_ticket,object,offset,(gateway_dictionary_next_parameters index release_parameters),
    (source_prefix++inserting++release_prefix),suffix,loop_memory,loop_world,(objects insert_next).
  split;[rewrite EVENTS,REST_EVENTS;repeat rewrite app_assoc;reflexivity|]. split.
  - intros descriptor;rewrite !gateway_received_append,
      (gateway_quiet_received io descriptor source_prefix PREFIX_QUIET),
      (gateway_object_run_no_direct_receive backend(Clight.globalenv prog)io gateway_api_dict_set insert_definition
        [Vptr parent parent_offset;Vptr key key_offset;Vptr object offset]insert_before insert_world inserting(Vint Int.zero)insert_after insert_next
        descriptor projection INSERT_DEFINITION INSERTING),(RELEASE_EMPTY descriptor);reflexivity.
  - split;[exact FRAMED|]. split;[exact CHILD_FRESH|]. split;[reflexivity|]. split;[exact FINAL_WELL|]. split.
    + unfold gateway_reference_loop_entries;rewrite FINAL_ENTRIES;exact ENTRIES.
    + split;[unfold gateway_dictionary_next_parameters;rewrite PTree.gso by discriminate;rewrite RELEASE_PARENT;exact CALLED_PARENT|].
      split;[unfold gateway_dictionary_next_parameters;rewrite PTree.gso by discriminate;rewrite RELEASE_STREAM,CALLED_STREAM;exact STREAM|].
      split;[unfold gateway_dictionary_next_parameters;rewrite PTree.gso by discriminate;rewrite RELEASE_DEPTH,CALLED_DEPTH;exact DEPTH|].
      split;[apply PTree.gss|]. split;[exact LOOP_RUN|]. split;[exact LOOP_READY|]. split;[exact DESCRIPTOR|].
      split;[exact UPDATED_LOOKUP|]. split;[exact UPDATED_FIELDS|]. split;assumption.
Qed.
