(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual append call supplies its own selected primitive, graph
   update and retained source-reference receipt. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Integers AST Values Memory Events Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences
  GatewayImport GatewayValue GatewayObjectThreads GatewayObjectDiscipline GatewayContainerGraph
  GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceHeld GatewayReferenceThreads
  GatewayReferenceContainers GatewayReferenceContainerScope GatewayOperations GatewayObjectExecution
  GatewayReadonly GatewayReturnRuntime GatewayThreadRuntime GatewayStreamInterface GatewayFramedRuntime.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_reference_actual_array_run {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (reference_threads:gateway_reference_thread_contract backend(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (containers:gateway_container_runtime backend python objects)
    ledger held parent_owner parent_ticket parent pointers values child child_value definition environment
    (property:Memory.mem->World->Prop)before world events after next:
  gateway_object_api_definition gateway_api_list_append=Some definition->gateway_ambient_closed backend property->
  (forall memory current,property memory current->
    gateway_reference_scope python objects decimal_float ledger held current /\
    gateway_reference_owns ledger parent_owner parent_ticket parent /\
    gateway_rooted(python current)(objects current)child /\
    gateway_private_tree(objects current)parent /\gateway_destructible(objects current)parent /\
    gateway_object_values(objects current)parent=Some(gateway_list_object pointers) /\
    gateway_array_heap decimal_float(objects current)pointers values /\
    gateway_private_tree(objects current)child /\gateway_destructible(objects current)child /\
    gateway_value_heap decimal_float(objects current)child child_value /\
    (forall pointer,In pointer(pointers++[child])->~gateway_object_reachable(objects current)pointer parent) /\
    (forall captured,In captured held->~gateway_object_reachable(objects current)(gateway_held_object captured)parent))->
  property before world->
  gateway_return_environment(fun current candidate=>gateway_native_private(python current)candidate)
    (gateway_python_discipline python objects detached)None environment before world->
  gateway_steps backend ge(gateway_live(Callstate definition[parent;child]Kstop before)world)events
    (gateway_live(Returnstate(Vint Int.zero)Kstop after)next)->
  gateway_reference_scope python objects decimal_float ledger
    (held++[gateway_reference_wire_capture parent_ticket parent
      (LeanCage_Host_GatewayResponseCode_Value_array(gateway_wire_values(values++[child_value])))])next /\
  gateway_object_values(objects next)parent=Some(gateway_list_object(pointers++[child])) /\
  (forall pointer,In pointer(pointers++[child])->~gateway_object_reachable(objects next)pointer parent) /\
  gateway_return_environment(fun current candidate=>gateway_native_private(python current)candidate)
    (gateway_python_discipline python objects detached)None environment after next /\
  exists prefix suffix called called_world changed changed_world observed,
    events=prefix++gateway_primitive observed::suffix /\
    gateway_object_operation backend gateway_api_list_append[parent;child]called called_world
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
  destruct(gateway_actual_object_operation backend ge gateway_api_list_append definition[parent;child]input
    before world events(Vint Int.zero)after next DEFINITION INPUT_CLOSED(conj GOOD INITIAL)RUN)
    as(prefix &suffix &called &called_world &changed &changed_world &observed &EVENTS &[PROP[READY ENV]]&OPERATION &PREFIX &SUFFIX).
  destruct(INPUTS called called_world PROP)as[SCOPE[PARENT_OWNED[CHILD_ROOT[PRIVATE[DESTROY[LOOKUP[ARRAY[CHILD_PRIVATE[CHILD_DESTROY[CHILD_VALUE[ACYCLIC OUTSIDE]]]]]]]]]]].
  assert(POSITIVE:(0<python_native_strong(python called_world)parent)%nat).
  { pose proof(gateway_reference_owned_count_positive _ _ _ _ PARENT_OWNED)as COUNT.
    pose proof(proj1 SCOPE parent)as FIT;lia. }
  destruct(gateway_reference_actual_append backend python objects containers decimal_float ledger held called called_world
    parent pointers values child child_value changed changed_world observed SCOPE READY POSITIVE CHILD_ROOT PRIVATE DESTROY
    LOOKUP ARRAY CHILD_PRIVATE CHILD_DESTROY CHILD_VALUE ACYCLIC OUTSIDE OPERATION)
    as[HELD_AFTER[VALUE_AFTER[PRIVATE_AFTER[DESTROY_AFTER[ACYCLIC_AFTER RETURN]]]]].
  set(captured:=gateway_reference_wire_capture parent_ticket parent
    (LeanCage_Host_GatewayResponseCode_Value_array(gateway_wire_values(values++[child_value])))).
  assert(SCOPE_AFTER:gateway_reference_scope python objects decimal_float ledger(held++[captured])changed_world).
  { eapply gateway_reference_add_wire_capture;[exact HELD_AFTER|exact PARENT_OWNED|exact PRIVATE_AFTER|exact DESTROY_AFTER|exact VALUE_AFTER]. }
  set(output:=fun memory current=>gateway_return_environment native base None environment memory current /\
    gateway_reference_scope python objects decimal_float ledger(held++[captured])current /\
    gateway_graph_region_frame(objects changed_world)(objects current)parent).
  assert(AFTER:output changed changed_world).
  { split.
    - split;[exact(gateway_container_ready _ _ _ _ _ _ _ _ RETURN)|].
      intros identifier object ty SELECTED;destruct(ENV identifier object ty SELECTED)as[LIVE NATIVE];split.
      + eapply Mem.valid_block_unchanged_on;[exact(gateway_container_native _ _ _ _ _ _ _ _ RETURN)|exact LIVE].
      + eapply gateway_container_native_retained;[exact RETURN|exact LIVE|exact NATIVE].
    - split;[exact SCOPE_AFTER|]. intros pointer REACHED;split;[intros;assumption|apply PRIVATE_AFTER;exact REACHED]. }
  assert(OUTPUT_CLOSED:gateway_ambient_closed backend output).
  { intros first current last following[READY_BEFORE[HELD_BEFORE GRAPH]]INTERFERENCE.
    pose proof(gateway_reference_thread_ambient _ _ _ _ _ _ _ reference_threads None first current last following
      (proj1 READY_BEFORE)INTERFERENCE)as EFFECT.
    split;[eapply gateway_return_environment_ambient;[exact runtime|exact READY_BEFORE|exact INTERFERENCE]|].
    split;[eapply gateway_reference_scope_thread_effect;[exact HELD_BEFORE|exact EFFECT]|].
    eapply gateway_graph_region_frame_trans;[exact GRAPH|].
    eapply(gateway_reference_thread_graph_frame python objects decimal_float ledger(held++[captured])current following captured);
      [exact HELD_BEFORE|apply in_or_app;right;left;reflexivity|exact EFFECT]. }
  pose proof(gateway_readonly_run_side backend ge output OUTPUT_CLOSED(Returnstate(Vint Int.zero)Kstop changed)changed_world
    suffix(Vint Int.zero)after next I AFTER SUFFIX)as[FINAL_ENV[FINAL_SCOPE GRAPH]].
  assert(FINAL_LOOKUP:gateway_object_values(objects next)parent=Some(gateway_list_object(pointers++[child]))).
  { apply(proj1(GRAPH parent(gateway_reachable_root _ _)));exact(gateway_container_value _ _ _ _ _ _ _ _ RETURN). }
  split;[exact FINAL_SCOPE|]. split;[exact FINAL_LOOKUP|]. split.
  - intros pointer MEMBER REACHED;apply(ACYCLIC_AFTER pointer MEMBER).
    assert(CHILD_REACHED:gateway_object_reachable(objects changed_world)parent pointer).
    { eapply gateway_reachable_child;[constructor|exact(gateway_container_value _ _ _ _ _ _ _ _ RETURN)|exact MEMBER]. }
    eapply gateway_graph_frame_reachable_back;[|eapply gateway_graph_region_frame_child;[exact GRAPH|exact CHILD_REACHED]|exact REACHED].
    intros object PATH;apply DESTROY_AFTER;eapply gateway_reachable_trans;eassumption.
  - split;[exact FINAL_ENV|]. exists prefix,suffix,called,called_world,changed,changed_world,observed;split;assumption.
Qed.
