(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The selected builtin child release consumes one source owner on
   the same actual SDK run, preserving separately held parent graphs and aliases. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences
  GatewayObjectThreads GatewayObjectDiscipline GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceHeld
  GatewayReferenceThreads GatewayOperations GatewayObjectExecution GatewayReadonly GatewayReturnRuntime
  GatewayThreadRuntime GatewayStreamInterface GatewayFramedRuntime.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_reference_actual_release_run {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (reference_threads:gateway_reference_thread_contract backend(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (references:gateway_reference_runtime backend python objects)
    ledger owner ticket pointer held definition environment(property:Memory.mem->World->Prop)before world events result after next:
  gateway_reference_ledger_well_formed ledger->gateway_object_api_definition gateway_api_decref=Some definition->
  gateway_ambient_closed backend property->
  (forall memory current,property memory current->gateway_reference_scope python objects decimal_float ledger held current /\
    gateway_reference_owns ledger owner ticket pointer /\gateway_destructible(objects current)pointer)->
  (forall captured,In captured held->gateway_held_ticket captured<>ticket)->
  property before world->gateway_return_environment(fun current candidate=>gateway_native_private(python current)candidate)
    (gateway_python_discipline python objects detached)None environment before world->
  gateway_steps backend ge(gateway_live(Callstate definition[pointer]Kstop before)world)events
    (gateway_live(Returnstate result Kstop after)next)->
  exists final prefix suffix called called_world changed changed_world observed,
    gateway_reference_apply(gateway_reference_release owner pointer)(gateway_reference_valid ledger)=gateway_reference_valid final /\
    gateway_reference_ledger_well_formed final /\gateway_reference_scope python objects decimal_float final held next /\
    gateway_return_environment(fun current candidate=>gateway_native_private(python current)candidate)
      (gateway_python_discipline python objects detached)None environment after next /\
    events=prefix++gateway_primitive observed::suffix /\
    gateway_object_operation backend gateway_api_decref[pointer]called called_world result changed changed_world observed /\
    (forall place other value,other<>ticket->gateway_reference_owns ledger place other value->gateway_reference_owns final place other value).
Proof.
  intros FORMED DEFINITION CLOSED INPUTS DIFFERENT GOOD INITIAL RUN.
  set(native:=fun current candidate=>gateway_native_private(python current)candidate).
  set(base:=gateway_python_discipline python objects detached).
  set(input:=fun memory current=>property memory current /\gateway_return_environment native base None environment memory current).
  assert(INPUT_CLOSED:gateway_ambient_closed backend input).
  { intros first current last following[PROP READY]INTERFERENCE;split.
    - eapply CLOSED;eassumption.
    - eapply gateway_return_environment_ambient;[exact runtime|exact READY|exact INTERFERENCE]. }
  destruct(gateway_actual_object_operation backend ge gateway_api_decref definition[pointer]input
    before world events result after next DEFINITION INPUT_CLOSED(conj GOOD INITIAL)RUN)
    as(prefix &suffix &called &called_world &changed &changed_world &observed &EVENTS &[PROP[READY ENV]]&OPERATION &PREFIX &SUFFIX).
  destruct(INPUTS called called_world PROP)as[[FIT HELD][OWNED DESTROY]].
  destruct(gateway_reference_decref_keeps_held backend python objects decimal_float references ledger owner ticket pointer
    called called_world result changed changed_world observed held FORMED FIT OWNED READY DESTROY HELD DIFFERENT OPERATION)
    as[final[RELEASE[WELL[COUNTS[HELD_AFTER RETURN]]]]].
  assert(RETAINED:forall place other value,other<>ticket->gateway_reference_owns ledger place other value->
    gateway_reference_owns final place other value).
  { destruct(gateway_reference_actual_decref backend python objects references ledger owner ticket pointer
      called called_world result changed changed_world observed FORMED FIT OWNED READY DESTROY OPERATION)
      as[selected[APPLY[WELL0[FIT0[RETURN0 OTHERS]]]]].
    rewrite RELEASE in APPLY;injection APPLY as SAME;subst selected;exact OTHERS. }
  set(output:=fun memory current=>gateway_return_environment native base None environment memory current /\
    gateway_reference_scope python objects decimal_float final held current).
  assert(AFTER:output changed changed_world).
  { split;[|exact(conj COUNTS HELD_AFTER)]. split;[exact(gateway_reference_ready _ _ _ _ _ _ _ RETURN)|].
    intros identifier object ty SELECTED;destruct(ENV identifier object ty SELECTED)as[LIVE NATIVE];split.
    - eapply Mem.valid_block_unchanged_on;[exact(gateway_reference_native _ _ _ _ _ _ _ RETURN)|exact LIVE].
    - eapply gateway_reference_native_retained;[exact RETURN|exact LIVE|exact NATIVE]. }
  assert(OUTPUT_CLOSED:gateway_ambient_closed backend output).
  { intros first current last following[READY_BEFORE HELD_BEFORE]INTERFERENCE;split.
    - eapply gateway_return_environment_ambient;[exact runtime|exact READY_BEFORE|exact INTERFERENCE].
    - eapply gateway_reference_scope_thread_effect;[exact HELD_BEFORE|].
      eapply gateway_reference_thread_ambient;[exact reference_threads|exact(proj1 READY_BEFORE)|exact INTERFERENCE]. }
  pose proof(gateway_readonly_run_side backend ge output OUTPUT_CLOSED(Returnstate result Kstop changed)changed_world
    suffix result after next I AFTER SUFFIX)as[FINAL_ENV FINAL_SCOPE].
  exists final,prefix,suffix,called,called_world,changed,changed_world,observed.
  exact(conj RELEASE(conj WELL(conj FINAL_SCOPE(conj FINAL_ENV(conj EVENTS(conj OPERATION RETAINED)))))).
Qed.
