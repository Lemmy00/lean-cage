(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual dictionary insertion supplies its own selected primitive, graph
   update and retained source-reference receipt. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Events Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences
  GatewayImport GatewayValue GatewayObjectThreads GatewayObjectDiscipline GatewayContainerGraph GatewayDictionarySeparation
  GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceHeld GatewayReferenceThreads
  GatewayReferenceDictionaries GatewayReferenceContainerScope GatewayContainerEffects GatewayContainerLength GatewayContainerGuards GatewayContainerMemory GatewayReferenceContainerContext GatewayOperations GatewayObjectExecution
  GatewayReadonly GatewayReturnRuntime GatewayThreadRuntime GatewayStreamInterface GatewayFramedRuntime.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_reference_actual_dictionary_context_run {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (reference_threads:gateway_reference_thread_contract backend(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (containers:gateway_container_runtime backend python objects)
    (excluded:Values.val->Prop)slots stream_block stream_offset initial readonly original size ledger held parent_owner parent_ticket parent fields entries key characters key_value child child_value definition environment
    (property:Memory.mem->World->Prop)before world events after next:
  gateway_object_api_definition gateway_api_dict_set=Some definition->gateway_ambient_closed backend property->
  (forall memory current,property memory current->
    gateway_reference_scope python objects decimal_float ledger held current /\
    gateway_reference_owns ledger parent_owner parent_ticket parent /\
    gateway_rooted(python current)(objects current)key /\gateway_rooted(python current)(objects current)child /\
    gateway_private_tree(objects current)parent /\gateway_destructible(objects current)parent /\
    gateway_object_values(objects current)parent=Some(gateway_dict_object fields) /\
    gateway_dictionary_heap decimal_float(objects current)fields entries /\
    gateway_object_values(objects current)key=Some(gateway_unicode_object characters) /\gateway_dictionary_lookup characters fields=None /\
    gateway_private_tree(objects current)key /\gateway_destructible(objects current)key /\
    gateway_value_heap decimal_float(objects current)key key_value /\
    gateway_private_tree(objects current)child /\gateway_destructible(objects current)child /\
    gateway_value_heap decimal_float(objects current)child child_value /\
    (forall pointer,In pointer(gateway_dictionary_children fields++[key;child])->~gateway_object_reachable(objects current)pointer parent) /\
    (forall captured,In captured held->~gateway_object_reachable(objects current)(gateway_held_object captured)parent) /\
    gateway_container_counted(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)gateway_container_object slots stream_block stream_offset initial readonly original size memory current /\
    (forall candidate position,readonly candidate position->gateway_native_private(python current)candidate) /\
    (forall pointer,excluded pointer->~gateway_object_reachable(objects current)parent pointer /\
      ~gateway_object_reachable(objects current)key pointer /\~gateway_object_reachable(objects current)child pointer))->
  property before world->
  gateway_return_environment(fun current candidate=>gateway_native_private(python current)candidate)
    (gateway_python_discipline python objects detached)None environment before world->
  gateway_steps backend ge(gateway_live(Callstate definition[parent;key;child]Kstop before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next)->
  gateway_reference_scope python objects decimal_float ledger
    (held++[gateway_reference_wire_capture parent_ticket parent
      (LeanCage_Host_GatewayResponseCode_Value_object(gateway_wire_fields(entries++[(key_value,child_value)])))])next /\
  gateway_object_values(objects next)parent=Some(gateway_dict_object(fields++[{|gateway_dictionary_key:=key;gateway_dictionary_text:=characters;gateway_dictionary_value:=child|}])) /\
  (forall pointer,In pointer(gateway_dictionary_children fields++[key;child])->~gateway_object_reachable(objects next)pointer parent) /\
  gateway_return_environment(fun current candidate=>gateway_native_private(python current)candidate)
    (gateway_python_discipline python objects detached)None environment after next /\
  gateway_container_counted(fun current candidate=>gateway_native_private(python current)candidate)stable
    (gateway_python_discipline python objects detached)gateway_container_object slots stream_block stream_offset initial readonly original size after next /\
  (forall candidate position,readonly candidate position->gateway_native_private(python next)candidate) /\
  (forall pointer,excluded pointer->~gateway_object_reachable(objects next)parent pointer) /\
  exists prefix suffix called called_world changed changed_world observed,
    events=prefix++gateway_primitive observed::suffix /\
    gateway_object_operation backend gateway_api_dict_set[parent;key;child]called called_world
      (Vint Int.zero)changed changed_world observed.
Proof.
  intros DEFINITION CLOSED INPUTS GOOD INITIAL RUN.
  set(native:=fun current candidate=>gateway_native_private(python current)candidate).
  set(base:=gateway_python_discipline python objects detached).
  set(input:=fun memory current=>property memory current /\gateway_return_environment native base None environment memory current).
  assert(INPUT_CLOSED:gateway_ambient_closed backend input).
  { intros first current last following[PROP READY]INTERFERENCE;split.
    - eapply CLOSED;eassumption.
    - eapply gateway_return_environment_ambient;[exact runtime|exact READY|exact INTERFERENCE]. }
  destruct(gateway_actual_object_operation backend ge gateway_api_dict_set definition[parent;key;child]input
    before world events(Vint Int.zero)after next DEFINITION INPUT_CLOSED(conj GOOD INITIAL)RUN)
    as(prefix &suffix &called &called_world &changed &changed_world &observed &EVENTS &[PROP[READY ENV]]&OPERATION &PREFIX &SUFFIX).
  destruct(INPUTS called called_world PROP)as(SCOPE &PARENT_OWNED &KEY_ROOT &CHILD_ROOT &PRIVATE &DESTROY &LOOKUP &FIELDS &KEY_LOOKUP &UNIQUE &KEY_PRIVATE &KEY_DESTROY &KEY_VALUE &CHILD_PRIVATE &CHILD_DESTROY &CHILD_VALUE &ACYCLIC &OUTSIDE &COUNTED &READONLY &EXCLUDED).
  assert(POSITIVE:(0<python_native_strong(python called_world)parent)%nat).
  { pose proof(gateway_reference_owned_count_positive _ _ _ _ PARENT_OWNED)as COUNT.
    pose proof(proj1 SCOPE parent)as FIT;lia. }
  destruct(gateway_reference_actual_dictionary_insert backend python objects containers decimal_float ledger held called called_world
    parent fields entries key characters key_value child child_value changed changed_world observed SCOPE READY POSITIVE KEY_ROOT CHILD_ROOT PRIVATE DESTROY
    LOOKUP FIELDS KEY_LOOKUP UNIQUE KEY_PRIVATE KEY_DESTROY KEY_VALUE CHILD_PRIVATE CHILD_DESTROY CHILD_VALUE ACYCLIC OUTSIDE OPERATION)
    as[HELD_AFTER[VALUE_AFTER[PRIVATE_AFTER[DESTROY_AFTER[ACYCLIC_AFTER RETURN]]]]].
  assert(NEXT_PARENT:gateway_rooted(python changed_world)(objects changed_world)parent).
  { apply gateway_direct_root;rewrite(gateway_container_references _ _ _ _ _ _ _ _ RETURN parent)
      by(intro MEMBER;inversion MEMBER);exact POSITIVE. }
  assert(EXCLUDED_AFTER:forall pointer,excluded pointer->~gateway_object_reachable(objects changed_world)parent pointer).
  { intros pointer FORBIDDEN;destruct(EXCLUDED pointer FORBIDDEN)as[PARENT_OUTSIDE[KEY_OUTSIDE CHILD_OUTSIDE]].
    assert(PARENT_ROOT:gateway_rooted(python called_world)(objects called_world)parent)
      by(eapply gateway_reference_owned_rooted;[exact(proj1 SCOPE)|exact PARENT_OWNED]).
    eapply gateway_dictionary_insert_separation;[exact LOOKUP|exact PRIVATE|exact DESTROY|exact KEY_PRIVATE|exact KEY_DESTROY|exact CHILD_PRIVATE|exact CHILD_DESTROY|
      exact PARENT_ROOT|exact KEY_ROOT|exact CHILD_ROOT|exact NEXT_PARENT|exact ACYCLIC|exact PARENT_OUTSIDE|exact KEY_OUTSIDE|exact CHILD_OUTSIDE|exact RETURN]. }
  destruct(gateway_container_mutation_retains backend python objects detached io stable thread_errno runtime gateway_container_object slots
    stream_block stream_offset initial readonly original size called called_world parent changed changed_world _ COUNTED READONLY RETURN)
    as[COUNTED_AFTER READONLY_AFTER].
  set(captured:=gateway_reference_wire_capture parent_ticket parent
    (LeanCage_Host_GatewayResponseCode_Value_object(gateway_wire_fields(entries++[(key_value,child_value)])))).
  assert(SCOPE_AFTER:gateway_reference_scope python objects decimal_float ledger(held++[captured])changed_world).
  { eapply gateway_reference_add_wire_capture;[exact HELD_AFTER|exact PARENT_OWNED|exact PRIVATE_AFTER|exact DESTROY_AFTER|exact VALUE_AFTER]. }
  set(output:=fun memory current=>gateway_return_environment native base None environment memory current /\
    gateway_reference_scope python objects decimal_float ledger(held++[captured])current /\
    gateway_graph_region_frame(objects changed_world)(objects current)parent /\
    gateway_container_counted native stable base gateway_container_object slots stream_block stream_offset initial readonly original size memory current /\
    (forall candidate position,readonly candidate position->native current candidate) /\
    (forall pointer,excluded pointer->~gateway_object_reachable(objects current)parent pointer)).
  assert(AFTER:output changed changed_world).
  { split.
    - split;[exact(gateway_container_ready _ _ _ _ _ _ _ _ RETURN)|].
      intros identifier object ty SELECTED;destruct(ENV identifier object ty SELECTED)as[LIVE NATIVE];split.
      + eapply Mem.valid_block_unchanged_on;[exact(gateway_container_native _ _ _ _ _ _ _ _ RETURN)|exact LIVE].
      + eapply gateway_container_native_retained;[exact RETURN|exact LIVE|exact NATIVE].
    - split;[exact SCOPE_AFTER|]. split.
      + intros pointer REACHED;split;[intros;assumption|apply PRIVATE_AFTER;exact REACHED].
      + exact(conj COUNTED_AFTER(conj READONLY_AFTER EXCLUDED_AFTER)). }
  assert(OUTPUT_CLOSED:gateway_ambient_closed backend output).
  { intros first current last following[READY_BEFORE[HELD_BEFORE[GRAPH[COUNTED_BEFORE[NATIVE_BEFORE EXCLUDED_BEFORE]]]]]INTERFERENCE.
    pose proof(gateway_reference_thread_ambient _ _ _ _ _ _ _ reference_threads None first current last following
      (proj1 READY_BEFORE)INTERFERENCE)as EFFECT.
    split;[eapply gateway_return_environment_ambient;[exact runtime|exact READY_BEFORE|exact INTERFERENCE]|].
    split;[eapply gateway_reference_scope_thread_effect;[exact HELD_BEFORE|exact EFFECT]|]. split.
    - eapply gateway_graph_region_frame_trans;[exact GRAPH|].
    eapply(gateway_reference_thread_graph_frame python objects decimal_float ledger(held++[captured])current following captured);
      [exact HELD_BEFORE|apply in_or_app;right;left;reflexivity|exact EFFECT].
    - pose proof(gateway_reference_counted_context_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation
        runtime reference_threads ledger(held++[captured])gateway_container_object slots stream_block stream_offset initial readonly original size
        first current last following(conj COUNTED_BEFORE(conj HELD_BEFORE NATIVE_BEFORE))INTERFERENCE)as[COUNTED_FINAL[HELD_FINAL NATIVE_FINAL]].
      split;[exact COUNTED_FINAL|]. split;[exact NATIVE_FINAL|].
      intros pointer FORBIDDEN;eapply(gateway_reference_thread_keeps_graph_exclusion python objects decimal_float ledger
        (held++[captured])current following captured pointer);
        [exact HELD_BEFORE|apply in_or_app;right;left;reflexivity|apply EXCLUDED_BEFORE;exact FORBIDDEN|exact EFFECT]. }
  pose proof(gateway_readonly_run_side backend ge output OUTPUT_CLOSED(Returnstate(Vint Int.zero)Kstop changed)changed_world
    suffix(Vint Int.zero)after next I AFTER SUFFIX)as[FINAL_ENV[FINAL_SCOPE[GRAPH[FINAL_COUNTED[FINAL_READONLY FINAL_EXCLUDED]]]]].
  assert(FINAL_LOOKUP:gateway_object_values(objects next)parent=Some(gateway_dict_object(fields++[{|gateway_dictionary_key:=key;gateway_dictionary_text:=characters;gateway_dictionary_value:=child|}]))).
  { apply(proj1(GRAPH parent(gateway_reachable_root _ _)));exact(gateway_container_value _ _ _ _ _ _ _ _ RETURN). }
  split;[exact FINAL_SCOPE|]. split;[exact FINAL_LOOKUP|]. split.
  - intros pointer MEMBER REACHED;apply(ACYCLIC_AFTER pointer MEMBER).
    assert(CHILD_REACHED:gateway_object_reachable(objects changed_world)parent pointer).
    { eapply gateway_reachable_child;[constructor|exact(gateway_container_value _ _ _ _ _ _ _ _ RETURN)|unfold gateway_object_children,gateway_dictionary_children;rewrite flat_map_app;cbn;exact MEMBER]. }
    eapply gateway_graph_frame_reachable_back;[|eapply gateway_graph_region_frame_child;[exact GRAPH|exact CHILD_REACHED]|exact REACHED].
    intros object PATH;apply DESTROY_AFTER;eapply gateway_reachable_trans;eassumption.
  - split;[exact FINAL_ENV|]. split;[exact FINAL_COUNTED|]. split;[exact FINAL_READONLY|]. split;[exact FINAL_EXCLUDED|]. exists prefix,suffix,called,called_world,changed,changed_world,observed;split;assumption.
Qed.
