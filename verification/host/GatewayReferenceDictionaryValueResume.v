(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Both recursive values, duplicate checks and selected cleanup
   compose on one dictionary execution, preserving its source objects and exact read bytes. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Machine CallContexts.
From HostGateway Require Import GatewaySource GatewayImport GatewayMachine GatewayPython GatewayObjects GatewayReferences
  GatewayObjectDiscipline GatewayObjectThreads GatewayObjectInstances GatewayValue GatewayValueEntry GatewayValueContext GatewayValueStack
  GatewayContainerLength GatewayContainerGuards GatewayContainerMemory GatewayContainerLoopSource GatewayContainerDictionarySource GatewayContainerChildContext GatewayContainerABI
  GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting GatewayReferenceThreads GatewayReferenceStackBound GatewayReferenceLoopLedger
  GatewayReferenceNormalForm GatewayReferenceDecoded GatewayReferenceParseResult GatewayReferenceParserInputs GatewayReferenceValueProperties GatewayReferenceAncestors GatewayReferenceSnapshotInputs
  GatewayReferenceGraphCapture GatewayReferenceContainerScope GatewayReferenceContainerContext GatewayReferenceEmptyContainer
  GatewayReferenceDictionaryKeyPhase GatewayReferenceDictionaryContainsPhase GatewayReferenceDictionarySecondInduction GatewayReferenceDictionarySecondResume
  GatewayReferenceDictionaryTarget GatewayContainerEncoding GatewayScalarDecoding GatewayThreadRuntime GatewayStreamInterface GatewayPathEvents GatewayObjectEvents.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_reference_actual_dictionary_value_resume {World Event}(backend:gateway_backend World Event)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (reference_threads:gateway_reference_thread_contract backend(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (containers:gateway_container_runtime backend python objects)(abi:gateway_container_abi_runtime backend python objects)
    (references:gateway_reference_runtime backend python objects)
    (instances:gateway_instance_runtime backend(Clight.globalenv prog)python objects(fun _ _ _=>Logic.False))
    (projection:gateway_direct_io_projection backend io)mode_symbol run_limit
    context older ledger held parent_ticket parent parent_offset fields entries parent_initial slots parameters depth index size
    stream_block stream_offset initial readonly original child_before child_world reading child child_after child_next events value after next:
  gateway_reference_short_parser backend python objects decimal_float detached io stable mode_symbol run_limit->
  gateway_reference_stack_bound context older->gateway_reference_ledger_well_formed ledger->
  gateway_reference_loop_entries context older ledger parent_ticket(Vptr parent parent_offset)->
  gateway_reference_graphs_only held->gateway_reference_snapshots_avoid held(Vptr parent parent_offset)->
  gateway_object_values parent_initial(Vptr parent parent_offset)=Some(gateway_dict_object fields)->
  gateway_dictionary_heap decimal_float parent_initial fields entries->
  (forall pointer,In pointer(gateway_dictionary_children fields)->~gateway_object_reachable parent_initial pointer(Vptr parent parent_offset))->
  (forall pointer,gateway_reference_mutable_target held pointer->~gateway_object_reachable parent_initial(Vptr parent parent_offset)pointer)->
  parameters!_container=Some(Vptr parent parent_offset)->parameters!_stream=Some(Vptr stream_block stream_offset)->
  parameters!_depth=Some(Vint depth)->parameters!_index__1=Some(Vlong index)->
  gateway_unicode_strict_mode original(Vptr mode_symbol Ptrofs.zero)->
  (forall object position,gateway_scalar_mode_region mode_symbol object position->readonly object position)->
  gateway_reference_counted_context python objects decimal_float detached stable ledger
    (held++[gateway_reference_graph_capture parent_ticket(Vptr parent parent_offset)
      (LeanCage_Host_GatewayResponseCode_Value_object(gateway_wire_fields entries))parent_initial])
    gateway_container_object slots stream_block stream_offset initial readonly original size child_before child_world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate(Internal f_host_value)[Vptr stream_block stream_offset;Vint(Int.sub depth Int.one)]Kstop child_before)child_world)reading
    (gateway_live(Returnstate child Kstop child_after)child_next)->
  gateway_reference_parse_result python objects decimal_float detached io stable(Clight.globalenv prog)
    (plug_cont(gateway_container_first_cont slots parameters)context)ledger
    (held++[gateway_reference_graph_capture parent_ticket(Vptr parent parent_offset)
      (LeanCage_Host_GatewayResponseCode_Value_object(gateway_wire_fields entries))parent_initial])
    stream_block stream_offset initial(gateway_container_child_readonly slots readonly)child_before reading child child_after child_next->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Returnstate child(gateway_container_first_cont slots parameters)child_after)child_next)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->(length events<=run_limit)%nat->
  exists final final_stream key_value child_value key key_offset object offset characters loop_parameters prefix suffix loop_memory loop_world parent_snapshot,
    events=prefix++suffix /\(0<length prefix)%nat /\
    gateway_response_frame(LeanCage_Host_GatewayResponseCode_Subject_value key_value)(gateway_received_bytes io(stream_descriptor initial)reading) /\
    gateway_response_frame(LeanCage_Host_GatewayResponseCode_Subject_value child_value)(gateway_received_bytes io(stream_descriptor initial)prefix) /\
    gateway_reference_ledger_well_formed final /\gateway_reference_loop_entries context older final parent_ticket(Vptr parent parent_offset) /\
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
    gateway_object_values parent_snapshot(Vptr parent parent_offset)=Some(gateway_dict_object(fields++[{|gateway_dictionary_key:=Vptr key key_offset;
      gateway_dictionary_text:=characters;gateway_dictionary_value:=Vptr object offset|}])) /\
    gateway_dictionary_heap decimal_float parent_snapshot(fields++[{|gateway_dictionary_key:=Vptr key key_offset;gateway_dictionary_text:=characters;
      gateway_dictionary_value:=Vptr object offset|}])(entries++[(key_value,child_value)]) /\
    (forall pointer,In pointer(gateway_dictionary_children(fields++[{|gateway_dictionary_key:=Vptr key key_offset;gateway_dictionary_text:=characters;
      gateway_dictionary_value:=Vptr object offset|}]))->~gateway_object_reachable parent_snapshot pointer(Vptr parent parent_offset)) /\
    (forall pointer,gateway_reference_mutable_target held pointer->~gateway_object_reachable parent_snapshot(Vptr parent parent_offset)pointer).
Proof.
  intros CHILDREN STACK FORMED ENTRIES GRAPHS OUTSIDE LOOKUP FIELDS ACYCLIC EXCLUDED PARENT STREAM DEPTH INDEX MODE MODE_SUBSET
    INPUT KEY_EXECUTION PARSED RUN NONNULL LIMIT.
  set(parent_capture:=gateway_reference_graph_capture parent_ticket(Vptr parent parent_offset)
    (LeanCage_Host_GatewayResponseCode_Value_object(gateway_wire_fields entries))parent_initial).
  destruct PARSED as(key_ledger &key_stream &key_value &key_ticket &DECODED &KEY_CONTEXT &KEY_NATIVE &KEY_DESCRIPTOR &KEY_FRAME).
  pose proof DECODED as[KEY_FORMED KEY_ENTRIES KEY_FRESH KEY_OWNER KEY_BOUND KEY_SCOPE KEY_VALUE KEY_AVOIDS].
  pose proof INPUT as[COUNTED[SCOPE NATIVE]].
  destruct(gateway_container_child_return(fun current candidate=>gateway_native_private(python current)candidate)stable
    (gateway_python_discipline python objects detached)gateway_container_object slots stream_block stream_offset initial key_stream readonly original size
    child_before child_world child_after child_next COUNTED KEY_CONTEXT KEY_NATIVE)as[RETURN_COUNTED RETURN_NATIVE].
  destruct(gateway_reference_owned_pointer python objects key_ledger _ _ child child_after child_next
    (proj1 KEY_CONTEXT)(proj1 KEY_SCOPE)KEY_OWNER)as(key &key_offset &KEY_POINTER &VALID);subst child.
  set(key_capture:=gateway_reference_graph_capture key_ticket(Vptr key key_offset)key_value(objects child_next)).
  assert(ALL_SCOPE:gateway_reference_scope python objects decimal_float key_ledger(held++[parent_capture;key_capture])child_next).
  { rewrite<-app_assoc in KEY_SCOPE;exact KEY_SCOPE. }
  assert(KEY_INPUT:gateway_reference_counted_context python objects decimal_float detached stable key_ledger(held++[parent_capture;key_capture])
    gateway_container_object slots stream_block stream_offset key_stream readonly original size child_after child_next)
    by(exact(conj RETURN_COUNTED(conj ALL_SCOPE RETURN_NATIVE))).
  assert(KEY_OUTSIDE:~gateway_object_reachable(objects child_next)(Vptr key key_offset)(Vptr parent parent_offset)).
  { apply(proj1(gateway_reference_avoids_targets _ _ _)KEY_AVOIDS).
    apply gateway_reference_dictionary_target with(fields:=fields);exact LOOKUP. }
  assert(KEY_EXCLUDED:forall pointer,gateway_reference_mutable_target held pointer->~gateway_object_reachable(objects child_next)(Vptr key key_offset)pointer).
  { intros pointer FORBIDDEN;apply(proj1(gateway_reference_avoids_targets _ _ _)KEY_AVOIDS).
    eapply gateway_reference_target_sublist;[intros captured MEMBER;apply in_or_app;left;exact MEMBER|exact FORBIDDEN]. }
  assert(OLD_KEY_TICKETS:forall captured,In captured held->gateway_held_ticket captured<>key_ticket).
  { intros captured MEMBER SAME.
    pose proof(gateway_reference_scope_ticket_bound python objects decimal_float ledger(held++[parent_capture])child_world captured FORMED SCOPE
      ltac:(apply in_or_app;left;exact MEMBER))as BELOW;lia. }
  assert(PARENT_KEY:parent_ticket<>key_ticket).
  { pose proof(gateway_reference_scope_ticket_bound python objects decimal_float ledger(held++[parent_capture])child_world parent_capture FORMED SCOPE
      ltac:(apply in_or_app;right;left;reflexivity))as BELOW;cbn in BELOW;lia. }
  destruct(gateway_reference_actual_dictionary_key_phase backend python objects decimal_float detached io stable thread_errno heap_allocation
    runtime reference_threads instances projection context older ledger key_ledger held parent_ticket parent parent_offset entries parent_initial
    key_ticket key key_offset key_value(objects child_next)slots parameters stream_block stream_offset key_stream readonly original size
    child_after child_next events value after next STACK KEY_FORMED ENTRIES KEY_ENTRIES KEY_INPUT RUN NONNULL)
    as(adopted &key_parameters &status &characters &key_prefix &key_suffix &key_memory &key_world &KEY_EVENTS &KEY_EMPTY &ADOPTED_FORMED &ADOPTED_ENTRIES &
      ADOPTED_NEXT &KEY_FIRST &KEY_PARENT &KEY_STREAM &KEY_DEPTH &KEY_INDEX &POSITIVE &KEY_LOOKUP &TO_KEY &KEY_READY &FROM_KEY).
  destruct(gateway_reference_actual_dictionary_contains_phase backend python objects decimal_float detached io stable thread_errno heap_allocation
    runtime reference_threads containers abi projection adopted held parent_ticket parent parent_offset fields entries parent_initial
    key_ticket key key_offset key_value(objects child_next)characters slots key_parameters status stream_block stream_offset key_stream readonly original size
    key_memory key_world key_suffix value after next ltac:(rewrite KEY_PARENT;exact PARENT)KEY_FIRST POSITIVE LOOKUP KEY_LOOKUP KEY_READY FROM_KEY NONNULL)
    as(contains_parameters &contains_prefix &contains_suffix &contains_memory &contains_world &CONTAINS_EVENTS &CONTAINS_EMPTY &STRING_KEY &CONTAINS_PARENT &
      CONTAINS_KEY &CONTAINS_STREAM &CONTAINS_DEPTH &CONTAINS_INDEX &UNIQUE &TO_CONTAINS &CONTAINS_READY &FROM_CONTAINS).
  assert(ALL_GRAPHS:gateway_reference_graphs_only(held++[parent_capture;key_capture])).
  { intros captured MEMBER;apply in_app_or in MEMBER;destruct MEMBER as[OLD|[SAME|[SAME|EMPTY]]];
      [apply GRAPHS;exact OLD|subst captured;eexists;eexists;reflexivity|subst captured;eexists;eexists;reflexivity|contradiction]. }
  assert(CONTAINS_LIMIT:(length contains_suffix<=run_limit)%nat).
  { rewrite KEY_EVENTS,CONTAINS_EVENTS,!length_app in LIMIT;lia. }
  assert(SECOND_PARENT:contains_parameters!_container=Some(Vptr parent parent_offset))by(rewrite CONTAINS_PARENT,KEY_PARENT;exact PARENT).
  assert(SECOND_KEY:contains_parameters!_first=Some(Vptr key key_offset))by(rewrite CONTAINS_KEY;exact KEY_FIRST).
  assert(SECOND_STREAM:contains_parameters!_stream=Some(Vptr stream_block stream_offset))by(rewrite CONTAINS_STREAM,KEY_STREAM;exact STREAM).
  assert(SECOND_DEPTH:contains_parameters!_depth=Some(Vint depth))by(rewrite CONTAINS_DEPTH,KEY_DEPTH;exact DEPTH).
  assert(SECOND_INDEX:contains_parameters!_index__1=Some(Vlong index))by(rewrite CONTAINS_INDEX,KEY_INDEX;exact INDEX).
  destruct(gateway_reference_actual_dictionary_second_induction backend python objects decimal_float detached io stable thread_errno heap_allocation
    runtime reference_threads mode_symbol run_limit context older adopted(held++[parent_capture;key_capture])parent_ticket parent parent_offset key_ticket key key_offset
    slots contains_parameters depth index status size stream_block stream_offset key_stream readonly original contains_memory contains_world contains_suffix value after next
    CHILDREN ADOPTED_FORMED ALL_GRAPHS MODE MODE_SUBSET CONTAINS_LIMIT STACK ADOPTED_ENTRIES SECOND_PARENT SECOND_KEY SECOND_STREAM SECOND_DEPTH SECOND_INDEX
    STRING_KEY POSITIVE CONTAINS_READY FROM_CONTAINS NONNULL)
    as(second_parameters &second_prefix &second_reading &second_suffix &second_before &second_world &second &second_after &second_next &SECOND_EVENTS &SECOND_QUIET &SHORT &
      CALLED_PARENT &CALLED_KEY &CALLED_STREAM &CALLED_DEPTH &CALLED_INDEX &TO_SECOND &SECOND_RUN &SECOND_NONNULL &FROM_SECOND &SECOND_READY &SECOND_STACK &SECOND_BOUND &
      SECOND_CONTEXT &SECOND_NATIVE &SECOND_PARSED).
  destruct(gateway_reference_actual_dictionary_second_resume backend python objects decimal_float detached io stable thread_errno heap_allocation
    runtime reference_threads containers abi references projection context older ledger adopted held parent_ticket parent parent_offset fields entries parent_initial
    key_ticket key key_offset key_value(objects child_next)characters slots second_parameters depth index size stream_block stream_offset key_stream readonly original
    second_before second_world second_reading second second_after second_next second_suffix value after next STACK ADOPTED_FORMED ENTRIES ADOPTED_ENTRIES KEY_FRESH
    OLD_KEY_TICKETS PARENT_KEY GRAPHS OUTSIDE LOOKUP FIELDS ACYCLIC EXCLUDED KEY_LOOKUP UNIQUE KEY_OUTSIDE KEY_EXCLUDED CALLED_PARENT CALLED_KEY CALLED_STREAM CALLED_DEPTH CALLED_INDEX
    SECOND_READY SECOND_RUN SECOND_PARSED FROM_SECOND NONNULL)
    as(final &final_stream &child_value &child_ticket &object &offset &loop_parameters &tail_prefix &suffix &loop_memory &loop_world &parent_snapshot &
      TAIL_EVENTS &TAIL_EMPTY &CHILD_FRAME &CHILD_FRESH &CHILD_POINTER &FINAL_FORMED &FINAL_ENTRIES &FINAL_PARENT &FINAL_STREAM &FINAL_DEPTH &FINAL_INDEX &LOOP_RUN &LOOP_READY &
      FINAL_DESCRIPTOR &FINAL_LOOKUP &FINAL_FIELDS &FINAL_ACYCLIC &FINAL_EXCLUDED).
  exists final,final_stream,key_value,child_value,key,key_offset,object,offset,characters,loop_parameters,
    (key_prefix++contains_prefix++second_prefix++second_reading++tail_prefix),suffix,loop_memory,loop_world,parent_snapshot.
  split;[rewrite KEY_EVENTS,CONTAINS_EVENTS,SECOND_EVENTS,TAIL_EVENTS;repeat rewrite app_assoc;reflexivity|]. split.
  - assert(POSITIVE_READ:(0<length second_reading)%nat)by(destruct second_reading;[inversion SECOND_RUN|cbn;lia]).
    rewrite !length_app;lia.
  - split;[exact KEY_FRAME|]. split.
    + rewrite !gateway_received_append,(KEY_EMPTY(stream_descriptor initial)),(CONTAINS_EMPTY(stream_descriptor initial)),
        (gateway_quiet_received io(stream_descriptor initial)second_prefix SECOND_QUIET),(TAIL_EMPTY(stream_descriptor initial));cbn.
      rewrite<-KEY_DESCRIPTOR;rewrite app_nil_r;exact CHILD_FRAME.
    + split;[exact FINAL_FORMED|]. split;[exact FINAL_ENTRIES|]. split;[exact FINAL_PARENT|]. split;[exact FINAL_STREAM|].
      split;[exact FINAL_DEPTH|]. split;[exact FINAL_INDEX|]. split;[exact LOOP_RUN|]. split;[exact LOOP_READY|].
      split;[rewrite FINAL_DESCRIPTOR;exact KEY_DESCRIPTOR|]. split;[exact FINAL_LOOKUP|]. split;[exact FINAL_FIELDS|]. split.
      * unfold gateway_dictionary_children;rewrite flat_map_app;cbn;exact FINAL_ACYCLIC.
      * exact FINAL_EXCLUDED.
Qed.
