(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The real array continuation releases only its selected child
   owner and advances the same source loop with its independently owned parent graph. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Ctypesdefs Clight.
Require Import Machine CallContexts.
From HostGateway Require Import GatewaySource GatewayImport GatewayMachine GatewayContexts GatewayPython GatewayObjects GatewayReferences
  GatewayObjectDiscipline GatewayObjectThreads GatewayValue GatewayValueEntry GatewayContainerLength GatewayContainerGuards GatewayContainerMemory
  GatewayContainerLoopSource GatewayContainerArraySource GatewayContainerArrayRelease GatewayContainerArrayStatus GatewaySourcePaths GatewaySourceSegments
  GatewayReferenceLedger GatewayReferenceAccounting GatewayReferencePlaces GatewayReferenceThreads GatewayReferenceNormalForm
  GatewayReferenceGraphCapture GatewayReferenceContainerScope GatewayReferenceContainerContext GatewayReferenceReleaseContextRun
  GatewayGraphSnapshots GatewayReadonly GatewayPathEvents GatewayReturnRuntime GatewayValueEnvironment GatewayThreadRuntime GatewayStreamInterface GatewayFramedRuntime.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_reference_actual_array_advance {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (reference_threads:gateway_reference_thread_contract backend(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (references:gateway_reference_runtime backend python objects)
    context parent_ledger ledger held parent_ticket parent parent_offset pointers values parent_initial child_ticket child child_offset
    slots parameters index stream_block stream_offset initial readonly original size before world events value after next release_symbol definition:
  gateway_reference_ledger_well_formed ledger->
  gateway_reference_entries ledger=gateway_reference_entry child_ticket
    (gateway_reference_temporary(gateway_reference_depth context)_first)(Vptr child child_offset)::gateway_reference_entries parent_ledger->
  (forall captured,In captured held->gateway_held_ticket captured<>child_ticket)->parent_ticket<>child_ticket->
  gateway_object_values parent_initial(Vptr parent parent_offset)=Some(gateway_list_object pointers)->In(Vptr child child_offset)pointers->
  parameters!_first=Some(Vptr child child_offset)->parameters!_index__1=Some(Vlong index)->
  gateway_reference_counted_context python objects decimal_float detached stable ledger
    (held++[gateway_reference_graph_capture parent_ticket(Vptr parent parent_offset)
      (LeanCage_Host_GatewayResponseCode_Value_array(gateway_wire_values values))parent_initial])
    gateway_container_array slots stream_block stream_offset initial readonly original size before world->
  gateway_object_api_definition gateway_api_decref=Some definition->
  Genv.find_symbol ge _Py_DecRef=Some release_symbol->Genv.find_funct_ptr ge release_symbol=Some definition->
  type_of_fundef definition=Tfunction[tptr(Tstruct __object noattr)]tvoid cc_default->
  gateway_steps backend ge
    (gateway_live(Returnstate(Vint Int.zero)(gateway_container_append_cont slots parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists final release_parameters prefix releasing advancing suffix release_before release_world released release_after release_next
    loop_memory loop_world,
    events=prefix++releasing++advancing++suffix /\Forall gateway_quiet_event prefix /\Forall gateway_quiet_event advancing /\
    gateway_reference_ledger_well_formed final /\
    gateway_reference_entries final=gateway_reference_entries parent_ledger /\
    gateway_reference_next final=gateway_reference_next ledger /\
    gateway_reference_apply(gateway_reference_release(gateway_reference_temporary(gateway_reference_depth context)_first)(Vptr child child_offset))
      (gateway_reference_valid ledger)=gateway_reference_valid final /\
    release_parameters!_result=Some(Vint Int.zero) /\release_parameters!_container=parameters!_container /\
    release_parameters!_first=parameters!_first /\release_parameters!_stream=parameters!_stream /\
    release_parameters!_depth=parameters!_depth /\release_parameters!_index__1=Some(Vlong index) /\
    gateway_steps backend ge
      (gateway_live(Returnstate(Vint Int.zero)(gateway_container_append_cont slots parameters)before)world)prefix
      (gateway_live(Callstate definition[Vptr child child_offset]
        (gateway_container_array_release_cont slots release_parameters)release_before)release_world) /\
    gateway_steps backend ge
      (gateway_live(Returnstate released(gateway_container_array_release_cont slots release_parameters)release_after)release_next)advancing
      (gateway_live(State f_host_value gateway_container_loop gateway_container_loop_cont(gateway_value_environment slots)
        (gateway_array_next_parameters index release_parameters)loop_memory)loop_world) /\
    gateway_steps backend ge
      (gateway_live(Callstate definition[Vptr child child_offset]Kstop release_before)release_world)releasing
      (gateway_live(Returnstate released Kstop release_after)release_next) /\
    gateway_steps backend ge
      (gateway_live(State f_host_value gateway_container_loop gateway_container_loop_cont(gateway_value_environment slots)
        (gateway_array_next_parameters index release_parameters)loop_memory)loop_world)suffix
      (gateway_live(Returnstate value Kstop after)next) /\
    gateway_reference_counted_context python objects decimal_float detached stable final
      (held++[gateway_reference_graph_capture parent_ticket(Vptr parent parent_offset)
        (LeanCage_Host_GatewayResponseCode_Value_array(gateway_wire_values values))parent_initial])
      gateway_container_array slots stream_block stream_offset initial readonly original size loop_memory loop_world.
Proof.
  intros FORMED ENTRIES OLD_TICKETS PARENT_TICKET LOOKUP CHILD_MEMBER FIRST INDEX INPUT DEFINITION SYMBOL FUNCTION TYPE RUN.
  set(native:=fun current candidate=>gateway_native_private(python current)candidate).
  set(base:=gateway_python_discipline python objects detached).
  set(parent_capture:=gateway_reference_graph_capture parent_ticket(Vptr parent parent_offset)
    (LeanCage_Host_GatewayResponseCode_Value_array(gateway_wire_values values))parent_initial).
  set(all_held:=held++[parent_capture]).
  set(property:=gateway_reference_counted_context python objects decimal_float detached stable ledger all_held gateway_container_array slots
    stream_block stream_offset initial readonly original size).
  pose proof(gateway_reference_counted_context_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation
    runtime reference_threads ledger all_held gateway_container_array slots stream_block stream_offset initial readonly original size)as CLOSED.
  destruct(gateway_container_append_release_owned_path backend ge property slots parameters Int.zero child child_offset before release_symbol definition
    CLOSED FIRST SYMBOL FUNCTION TYPE)as[release_parameters[PATH[RESULT[CALLED_PARENT[CALLED_FIRST[CALLED_STREAM[CALLED_DEPTH CALLED_INDEX]]]]]]].
  destruct(gateway_source_path_cut backend ge _ _ _ _ _ _ PATH before world events value after next INPUT RUN)
    as(prefix &rest &release_before &release_world &EVENTS &QUIET &PREFIX &CALLED &FROM_RELEASE).
  destruct(gateway_return_cut backend ge definition[Vptr child child_offset]
    (gateway_container_array_release_cont slots release_parameters)release_before release_world rest(Returnstate value Kstop after)next
    ltac:(cbn;exact I)ltac:(cbn;lia)FROM_RELEASE)
    as(releasing &tail &released &release_after &release_next &REST_EVENTS &RELEASE_RUN &REST).
  assert(CHILD_OWNED:gateway_reference_owns ledger(gateway_reference_temporary(gateway_reference_depth context)_first)
    child_ticket(Vptr child child_offset)).
  { unfold gateway_reference_owns;rewrite ENTRIES;left;reflexivity. }
  destruct(gateway_reference_actual_release_context_run backend ge python objects decimal_float detached io stable thread_errno heap_allocation
    runtime reference_threads references gateway_container_array slots stream_block stream_offset initial readonly original size ledger
    (gateway_reference_temporary(gateway_reference_depth context)_first)child_ticket(Vptr child child_offset)all_held definition
    (gateway_value_environment slots)property release_before release_world releasing released release_after release_next FORMED DEFINITION CLOSED
    ltac:(intros memory current[COUNTED[SCOPE NATIVE]];
      pose proof(gateway_reference_capture_member _ _ _ _ _ _ _ SCOPE
        ltac:(unfold all_held;apply in_or_app;right;left;reflexivity))
        as[OWNER[PRIVATE[DESTROY[VALUE[INITIAL SNAPSHOT]]]]];
      assert(CHILD_REACHED:gateway_object_reachable(objects current)(Vptr parent parent_offset)(Vptr child child_offset))by
        (eapply gateway_reachable_child;[constructor|rewrite SNAPSHOT by constructor;exact LOOKUP|exact CHILD_MEMBER]);
      assert(CHILD_DESTRUCTIBLE:gateway_destructible(objects current)(Vptr child child_offset))by
        (intros object LATER;apply DESTROY;eapply gateway_reachable_trans;eassumption);
      exact(conj SCOPE(conj CHILD_OWNED(conj CHILD_DESTRUCTIBLE(conj COUNTED NATIVE)))))
    ltac:(intros captured MEMBER;unfold all_held in MEMBER;apply in_app_or in MEMBER;destruct MEMBER as[OLD|[SAME|EMPTY]];
      [apply OLD_TICKETS;exact OLD|subst captured;exact PARENT_TICKET|contradiction])CALLED
    ltac:(destruct CALLED as[COUNTED OTHER];eapply gateway_value_active_environment;exact(proj1(proj1 COUNTED)))RELEASE_RUN)
    as(final &operation_prefix &operation_suffix &called &called_world &changed &changed_world &observed &RELEASE &WELL &SCOPE_AFTER &ENV_AFTER &
      COUNTED_AFTER &NATIVE_AFTER &OP_EVENTS &OPERATION &RETAINED).
  destruct(gateway_reference_head_release ledger final(gateway_reference_entries parent_ledger)child_ticket
    (gateway_reference_temporary(gateway_reference_depth context)_first)(Vptr child child_offset)ENTRIES RELEASE)as[FINAL_ENTRIES FINAL_NEXT].
  set(final_property:=gateway_reference_counted_context python objects decimal_float detached stable final all_held gateway_container_array slots
    stream_block stream_offset initial readonly original size).
  pose proof(gateway_reference_counted_context_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation
    runtime reference_threads final all_held gateway_container_array slots stream_block stream_offset initial readonly original size)as FINAL_CLOSED.
  pose proof(gateway_container_array_next_segment backend ge final_property slots release_parameters released index release_after
    FINAL_CLOSED RESULT ltac:(rewrite CALLED_INDEX;exact INDEX))as SEGMENT.
  destruct(gateway_source_segment_cut backend ge _ _ _ _ SEGMENT release_after release_next tail value after next
    (conj COUNTED_AFTER(conj SCOPE_AFTER NATIVE_AFTER))REST)
    as(advancing &suffix &loop_memory &loop_world &ADVANCE_EVENTS &ADVANCE_QUIET &ADVANCE &LOOP_READY &LOOP_RUN).
  exists final,release_parameters,prefix,releasing,advancing,suffix,release_before,release_world,released,release_after,release_next,loop_memory,loop_world.
  split;[rewrite EVENTS,REST_EVENTS,ADVANCE_EVENTS;repeat rewrite app_assoc;reflexivity|].
  split;[exact QUIET|]. split;[exact ADVANCE_QUIET|]. split;[exact WELL|]. split;[exact FINAL_ENTRIES|]. split;[exact FINAL_NEXT|]. split;[exact RELEASE|].
  split;[exact RESULT|]. split;[exact CALLED_PARENT|]. split;[exact CALLED_FIRST|]. split;[exact CALLED_STREAM|]. split;[exact CALLED_DEPTH|].
  split;[rewrite CALLED_INDEX;exact INDEX|]. split;[exact PREFIX|]. split;[exact ADVANCE|]. split;[exact RELEASE_RUN|]. split;[exact LOOP_RUN|exact LOOP_READY].
Qed.
