(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: A JSON float uses the actual retained decoded Unicode operand
   and the same single CPython decimal-to-binary operation; source syntax is proved separately. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayObjectDiscipline
  GatewayObjectThreads GatewayReferenceLedger GatewayReferenceThreads GatewayReferenceNumericRequests GatewayReferenceNumericStorage
  GatewayScalarLength GatewayScalarConstructorCalls GatewayOperations GatewayObjectExecution GatewayFramedRuntime GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_reference_actual_float_storage {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects detached io stable thread_errno heap_allocation decimal_float
    (runtime:gateway_thread_runtime backend io(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (constructors:gateway_objects_runtime backend python objects decimal_float)
    (reference_threads:gateway_reference_thread_contract backend(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    ledger owner held text_ticket text characters definition scalar slots stream_block stream_offset initial readonly original size object bytes
    before world events result after next:
  gateway_reference_ledger_well_formed ledger->gateway_reference_take owner(gateway_reference_entries ledger)=None->
  gateway_reference_scope python objects decimal_float ledger held world->
  In(gateway_reference_scalar_capture text_ticket text(gateway_unicode_object characters))held->
  gateway_object_api_definition gateway_api_float_string=Some definition->
  gateway_scalar_private_ready python objects detached stable heap_allocation scalar slots stream_block stream_offset initial readonly original size object bytes before world->
  gateway_steps backend ge(gateway_live(Callstate definition[text]Kstop before)world)events
    (gateway_live(Returnstate result Kstop after)next)->result<>Vnullptr->
  exists floating final,
    decimal_float characters floating /\
    gateway_reference_apply(gateway_reference_mint owner result)(gateway_reference_valid ledger)=gateway_reference_valid final /\
    gateway_reference_ledger_well_formed final /\gateway_reference_owns final owner(gateway_reference_next ledger)result /\
    gateway_scalar_private_ready python objects detached stable heap_allocation scalar slots stream_block stream_offset initial readonly original size object bytes after next /\
    gateway_reference_scope python objects decimal_float final(held++[gateway_reference_scalar_capture(gateway_reference_next ledger)result(gateway_float_object floating)])next.
Proof.
  intros FORMED VACANT SCOPE MEMBER DEFINITION INPUT RUN NONNULL.
  set(storage:=gateway_scalar_private_ready python objects detached stable heap_allocation scalar slots stream_block stream_offset initial readonly original size object bytes).
  set(property:=fun memory current=>storage memory current /\gateway_reference_scope python objects decimal_float ledger held current).
  pose proof(gateway_scalar_private_ambient backend python objects detached io stable thread_errno runtime heap_allocation scalar slots
    stream_block stream_offset initial readonly original size object bytes)as STORAGE_CLOSED.
  assert(CLOSED:gateway_ambient_closed backend property).
  { intros first current last following[READY HELD]INTERFERENCE;split.
    - eapply STORAGE_CLOSED;eassumption.
    - eapply gateway_reference_scope_thread_effect;[exact HELD|].
      eapply gateway_reference_thread_ambient;[exact reference_threads|eapply gateway_scalar_private_side;exact READY|exact INTERFERENCE]. }
  destruct(gateway_actual_object_operation backend ge gateway_api_float_string definition[text]property before world events result after next
    DEFINITION CLOSED(conj INPUT SCOPE)RUN)
    as(prefix &suffix &called &called_world &changed &changed_world &observed &EVENTS &[CALLED CALLED_SCOPE]&OPERATION &PREFIX &SUFFIX).
  destruct(gateway_reference_scalar_capture_value _ _ _ _ _ _ _ _ _ CALLED_SCOPE MEMBER)as[TEXT_ROOT[TEXT_VALUE REST]].
  destruct(gateway_runtime_float_constructor _ _ _ _ constructors called called_world text characters result changed changed_world observed
    ltac:(eapply gateway_scalar_private_side;exact CALLED)TEXT_ROOT TEXT_VALUE OPERATION NONNULL)as[floating[DECIMAL RETURN]].
  destruct(gateway_reference_actual_numeric_storage backend ge python objects detached io stable thread_errno heap_allocation decimal_float runtime constructors reference_threads
    ledger owner held gateway_api_float_string definition[text](gateway_float_object floating)gateway_float_kind scalar slots stream_block stream_offset initial readonly original
    size object bytes before world events result after next FORMED VACANT SCOPE DEFINITION
    ltac:(intros memory current READY SCOPE_NOW;
      destruct(gateway_reference_scalar_capture_value _ _ _ _ _ _ _ _ _ SCOPE_NOW MEMBER)as[ROOT[VALUE OTHER]];
      split;[apply gateway_request_float_string with(characters:=characters);assumption|exact ROOT])eq_refl eq_refl
    ltac:(unfold gateway_destructor_kind;auto 9)INPUT RUN NONNULL)
    as(final &MINT &WELL &OWNED &READY &FINAL_SCOPE).
  exists floating,final;exact(conj DECIMAL(conj MINT(conj WELL(conj OWNED(conj READY FINAL_SCOPE))))).
Qed.
