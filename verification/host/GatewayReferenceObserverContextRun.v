(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A source-selected builtin observer retains the actual counted
   stream and source references; its semantic fact comes from that same primitive occurrence. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Values Memory Integers AST Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayObjectDiscipline GatewayObjectThreads
  GatewayReferenceLedger GatewayReferenceThreads GatewayReferenceContainerContext GatewayReferenceObservers
  GatewayContainerLength GatewayContainerMemory GatewayObserverEffects GatewayOperations GatewayObjectExecution
  GatewayReturnRuntime GatewayReadonly GatewayThreadRuntime GatewayFramedRuntime.
Import ListNotations.

Theorem gateway_reference_actual_observer_context_run {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (reference_threads:gateway_reference_thread_contract backend(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    api definition arguments returned(Fact:Prop)ledger held container slots stream_block stream_offset initial readonly original size environment
    (property:mem->World->Prop)before world events after next:
  gateway_object_api_definition api=Some definition->gateway_ambient_closed backend property->
  (forall memory current,property memory current->
    gateway_reference_counted_context python objects decimal_float detached stable ledger held container slots
      stream_block stream_offset initial readonly original size memory current)->
  (forall memory current changed following observed,property memory current->
    gateway_object_operation backend api arguments memory current returned changed following observed->
    Fact /\gateway_observer_return(python current)(objects current)memory(python following)(objects following)changed)->
  property before world->
  gateway_return_environment(fun current candidate=>gateway_native_private(python current)candidate)
    (gateway_python_discipline python objects detached)None environment before world->
  gateway_steps backend ge(gateway_live(Callstate definition arguments Kstop before)world)events
    (gateway_live(Returnstate returned Kstop after)next)->
  Fact /\gateway_reference_counted_context python objects decimal_float detached stable ledger held container slots
    stream_block stream_offset initial readonly original size after next /\
  gateway_return_environment(fun current candidate=>gateway_native_private(python current)candidate)
    (gateway_python_discipline python objects detached)None environment after next /\
  exists prefix suffix called called_world changed changed_world observed,
    events=prefix++gateway_primitive observed::suffix /\
    property called called_world /\
    gateway_object_operation backend api arguments called called_world returned changed changed_world observed.
Proof.
  intros DEFINITION CLOSED INPUTS OPERATION GOOD INITIAL RUN.
  set(native:=fun current candidate=>gateway_native_private(python current)candidate).
  set(base:=gateway_python_discipline python objects detached).
  set(input:=fun memory current=>property memory current /\gateway_return_environment native base None environment memory current).
  assert(INPUT_CLOSED:gateway_ambient_closed backend input).
  { intros first current last following[PROP READY]INTERFERENCE;split.
    - eapply CLOSED;eassumption.
    - eapply gateway_return_environment_ambient;[exact runtime|exact READY|exact INTERFERENCE]. }
  destruct(gateway_actual_object_operation backend ge api definition arguments input before world events returned after next
    DEFINITION INPUT_CLOSED(conj GOOD INITIAL)RUN)
    as(prefix &suffix &called &called_world &changed &changed_world &observed &EVENTS &[PROP[READY ENV]]&ACTUAL &PREFIX &SUFFIX).
  destruct(OPERATION called called_world changed changed_world observed PROP ACTUAL)as[FACT EFFECT].
  pose proof(INPUTS called called_world PROP)as[COUNTED[SCOPE NATIVE]].
  destruct(gateway_observer_counted_retains backend python objects detached io stable thread_errno runtime container slots
    stream_block stream_offset initial readonly original size called called_world changed changed_world COUNTED NATIVE EFFECT)
    as[COUNTED_AFTER NATIVE_AFTER].
  pose proof(gateway_reference_observer_scope python objects decimal_float ledger held called_world changed_world called changed SCOPE EFFECT)as SCOPE_AFTER.
  assert(ENV_AFTER:gateway_return_environment native base None environment changed changed_world).
  { split;[exact(gateway_observer_ready _ _ _ _ _ _ EFFECT)|].
    intros identifier object ty SELECTED;destruct(ENV identifier object ty SELECTED)as[LIVE PRIVATE];split.
    - eapply Mem.valid_block_unchanged_on;[exact(gateway_observer_native _ _ _ _ _ _ EFFECT)|exact LIVE].
    - eapply gateway_observer_native_retained;[exact EFFECT|exact LIVE|exact PRIVATE]. }
  set(output:=fun memory current=>gateway_reference_counted_context python objects decimal_float detached stable ledger held container slots
    stream_block stream_offset initial readonly original size memory current /\gateway_return_environment native base None environment memory current).
  assert(OUTPUT_CLOSED:gateway_ambient_closed backend output).
  { intros first current last following[COUNTED_BEFORE ENV_BEFORE]INTERFERENCE;split.
    - eapply gateway_reference_counted_context_ambient;[exact runtime|exact reference_threads|exact COUNTED_BEFORE|exact INTERFERENCE].
    - eapply gateway_return_environment_ambient;[exact runtime|exact ENV_BEFORE|exact INTERFERENCE]. }
  pose proof(gateway_readonly_run_side backend ge output OUTPUT_CLOSED(Returnstate returned Kstop changed)changed_world suffix returned after next I
    (conj(conj COUNTED_AFTER(conj SCOPE_AFTER NATIVE_AFTER))ENV_AFTER)SUFFIX)as[FINAL_CONTEXT FINAL_ENV].
  split;[exact FACT|]. split;[exact FINAL_CONTEXT|]. split;[exact FINAL_ENV|].
  exists prefix,suffix,called,called_world,changed,changed_world,observed;exact(conj EVENTS(conj PROP ACTUAL)).
Qed.
