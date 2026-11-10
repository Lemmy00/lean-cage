(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: An actual numeric operand release consumes its selected source
   credit while retaining other scalar/graph references and the same live native buffer. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayObjectDiscipline
  GatewayObjectThreads GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceHeld GatewayReferenceThreads GatewayReferenceContainerScope
  GatewayReferenceNumericRequests GatewayScalarLength GatewayScalarTerminate GatewayScalarConstructorCalls GatewayScalarReleaseMemory
  GatewayOperations GatewayObjectExecution GatewayReadonly GatewayFramedRuntime GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_reference_actual_numeric_release {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects detached io stable thread_errno heap_allocation decimal_float
    (runtime:gateway_thread_runtime backend io(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (references:gateway_reference_runtime backend python objects)
    (reference_threads:gateway_reference_thread_contract backend(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    ledger owner ticket pointer description held definition scalar slots stream_block stream_offset initial readonly original size object bytes
    before world events result after next:
  gateway_reference_ledger_well_formed ledger->gateway_reference_owns ledger owner ticket pointer->
  (forall captured,In captured held->gateway_held_ticket captured<>ticket)->
  gateway_reference_scope python objects decimal_float ledger(held++[gateway_reference_scalar_capture ticket pointer description])world->
  gateway_object_api_definition gateway_api_decref=Some definition->
  gateway_scalar_private_ready python objects detached stable heap_allocation scalar slots stream_block stream_offset initial readonly original size object bytes before world->
  gateway_steps backend ge(gateway_live(Callstate definition[pointer]Kstop before)world)events
    (gateway_live(Returnstate result Kstop after)next)->
  exists final,
    gateway_reference_apply(gateway_reference_release owner pointer)(gateway_reference_valid ledger)=gateway_reference_valid final /\
    gateway_reference_ledger_well_formed final /\gateway_reference_scope python objects decimal_float final held next /\
    gateway_scalar_private_ready python objects detached stable heap_allocation scalar slots stream_block stream_offset initial readonly original size object bytes after next /\
    exists prefix suffix called called_world changed changed_world observed,
      events=prefix++gateway_primitive observed::suffix /\
      gateway_object_operation backend gateway_api_decref[pointer]called called_world result changed changed_world observed.
Proof.
  intros FORMED OWNED DIFFERENT SCOPE DEFINITION INPUT RUN.
  set(storage:=gateway_scalar_private_ready python objects detached stable heap_allocation scalar slots stream_block stream_offset initial readonly original size object bytes).
  set(all_held:=held++[gateway_reference_scalar_capture ticket pointer description]).
  pose proof(gateway_scalar_private_ambient backend python objects detached io stable thread_errno runtime heap_allocation scalar slots
    stream_block stream_offset initial readonly original size object bytes)as STORAGE_CLOSED.
  set(property:=fun memory current=>storage memory current /\gateway_reference_scope python objects decimal_float ledger all_held current).
  assert(CLOSED:gateway_ambient_closed backend property).
  { intros first current last following[READY HELD]INTERFERENCE;split.
    - eapply STORAGE_CLOSED;eassumption.
    - eapply gateway_reference_scope_thread_effect;[exact HELD|].
      eapply gateway_reference_thread_ambient;[exact reference_threads|eapply gateway_scalar_private_side;exact READY|exact INTERFERENCE]. }
  destruct(gateway_actual_object_operation backend ge gateway_api_decref definition[pointer]property before world events result after next
    DEFINITION CLOSED(conj INPUT SCOPE)RUN)
    as(prefix &suffix &called &called_world &changed &changed_world &observed &EVENTS &[CALLED CALLED_SCOPE]&OPERATION &PREFIX &SUFFIX).
  pose proof(gateway_reference_capture_member _ _ _ _ _ _ _ CALLED_SCOPE ltac:(unfold all_held;apply in_or_app;right;left;reflexivity))
    as[CAPTURED[PRIVATE[DESTROY VALUE]]].
  assert(SUBSET:gateway_reference_scope python objects decimal_float ledger held called_world).
  { eapply gateway_reference_scope_sublist;[exact CALLED_SCOPE|]. intros captured MEMBER;unfold all_held;apply in_or_app;left;exact MEMBER. }
  assert(SIDE:gateway_objects_ready(python called_world)(objects called_world)called)by(eapply gateway_scalar_private_side;exact CALLED).
  destruct(gateway_reference_decref_keeps_held backend python objects decimal_float references ledger owner ticket pointer called called_world
    result changed changed_world observed held FORMED(proj1 SUBSET)OWNED SIDE DESTROY(proj2 SUBSET)DIFFERENT OPERATION)
    as(final &RELEASE &WELL &FIT &HELD_AFTER &RETURN).
  destruct(gateway_scalar_release_retains backend python objects detached io stable thread_errno runtime heap_allocation scalar slots stream_block stream_offset initial readonly original
    size object bytes called called_world pointer changed changed_world(proj1 CALLED)(proj2 CALLED)RETURN)as[STORAGE_AFTER NATIVE_AFTER].
  set(output:=fun memory current=>storage memory current /\gateway_reference_scope python objects decimal_float final held current).
  assert(OUTPUT_CLOSED:gateway_ambient_closed backend output).
  { intros first current last following[READY HELD]INTERFERENCE;split.
    - eapply STORAGE_CLOSED;eassumption.
    - eapply gateway_reference_scope_thread_effect;[exact HELD|].
      eapply gateway_reference_thread_ambient;[exact reference_threads|eapply gateway_scalar_private_side;exact READY|exact INTERFERENCE]. }
  pose proof(gateway_readonly_run_side backend ge output OUTPUT_CLOSED(Returnstate result Kstop changed)changed_world suffix result after next I
    (conj(conj STORAGE_AFTER NATIVE_AFTER)(conj FIT HELD_AFTER))SUFFIX)as[FINAL_STORAGE FINAL_SCOPE].
  exists final;split;[exact RELEASE|]. split;[exact WELL|]. split;[exact FINAL_SCOPE|]. split;[exact FINAL_STORAGE|].
  exists prefix,suffix,called,called_world,changed,changed_world,observed;split;assumption.
Qed.
