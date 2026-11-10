(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Arbitrary-size integer SDK operations consume the same
   retained builtin operands at the selected source call, including cached aliases. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayObjectDiscipline
  GatewayObjectThreads GatewayReferenceLedger GatewayReferenceThreads GatewayReferenceNumericStorage GatewayReferenceNumericRequests
  GatewayScalarConstructorCalls GatewayScalarLength GatewayFramedRuntime GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Theorem gateway_reference_actual_binary_storage {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (constructors:gateway_objects_runtime backend python objects decimal_float)
    (reference_threads:gateway_reference_thread_contract backend(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (multiply:bool)ledger owner held definition left_ticket left first right_ticket right second
    scalar slots stream_block stream_offset initial readonly original size object bytes before world events result after next:
  gateway_reference_ledger_well_formed ledger->gateway_reference_take owner(gateway_reference_entries ledger)=None->
  gateway_reference_scope python objects decimal_float ledger held world->
  In(gateway_reference_scalar_capture left_ticket left(gateway_long_object first))held->
  In(gateway_reference_scalar_capture right_ticket right(gateway_long_object second))held->
  gateway_object_api_definition(if multiply then gateway_api_number_multiply else gateway_api_number_add)=Some definition->
  gateway_scalar_private_ready python objects detached stable heap_allocation scalar slots stream_block stream_offset initial readonly original
    size object bytes before world->
  gateway_steps backend ge(gateway_live(Callstate definition[left;right]Kstop before)world)events
    (gateway_live(Returnstate result Kstop after)next)->result<>Vnullptr->
  exists final,
    gateway_reference_apply(gateway_reference_mint owner result)(gateway_reference_valid ledger)=gateway_reference_valid final /\
    gateway_reference_ledger_well_formed final /\gateway_reference_owns final owner(gateway_reference_next ledger)result /\
    gateway_scalar_private_ready python objects detached stable heap_allocation scalar slots stream_block stream_offset initial readonly original
      size object bytes after next /\
    gateway_reference_scope python objects decimal_float final
      (held++[gateway_reference_scalar_capture(gateway_reference_next ledger)result
        (gateway_long_object(if multiply then first*second else first+second))])next.
Proof.
  intros FORMED VACANT SCOPE LEFT RIGHT DEFINITION INPUT RUN NONNULL.
  eapply gateway_reference_actual_numeric_storage;
    [exact runtime|exact constructors|exact reference_threads|exact FORMED|exact VACANT|exact SCOPE|exact DEFINITION|
     |reflexivity|reflexivity|unfold gateway_destructor_kind;auto 9|exact INPUT|exact RUN|exact NONNULL].
  intros memory current READY HOLD;destruct multiply.
  - eapply gateway_reference_multiply_request;[exact HOLD|exact LEFT|exact RIGHT].
  - eapply gateway_reference_add_request;[exact HOLD|exact LEFT|exact RIGHT].
Qed.

Theorem gateway_reference_actual_negative_storage {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (constructors:gateway_objects_runtime backend python objects decimal_float)
    (reference_threads:gateway_reference_thread_contract backend(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    ledger owner held definition ticket operand integer scalar slots stream_block stream_offset initial readonly original size object bytes
    before world events result after next:
  gateway_reference_ledger_well_formed ledger->gateway_reference_take owner(gateway_reference_entries ledger)=None->
  gateway_reference_scope python objects decimal_float ledger held world->
  In(gateway_reference_scalar_capture ticket operand(gateway_long_object integer))held->
  gateway_object_api_definition gateway_api_number_negative=Some definition->
  gateway_scalar_private_ready python objects detached stable heap_allocation scalar slots stream_block stream_offset initial readonly original
    size object bytes before world->
  gateway_steps backend ge(gateway_live(Callstate definition[operand]Kstop before)world)events
    (gateway_live(Returnstate result Kstop after)next)->result<>Vnullptr->
  exists final,
    gateway_reference_apply(gateway_reference_mint owner result)(gateway_reference_valid ledger)=gateway_reference_valid final /\
    gateway_reference_ledger_well_formed final /\gateway_reference_owns final owner(gateway_reference_next ledger)result /\
    gateway_scalar_private_ready python objects detached stable heap_allocation scalar slots stream_block stream_offset initial readonly original
      size object bytes after next /\
    gateway_reference_scope python objects decimal_float final
      (held++[gateway_reference_scalar_capture(gateway_reference_next ledger)result(gateway_long_object(-integer))])next.
Proof.
  intros FORMED VACANT SCOPE MEMBER DEFINITION INPUT RUN NONNULL.
  eapply gateway_reference_actual_numeric_storage;
    [exact runtime|exact constructors|exact reference_threads|exact FORMED|exact VACANT|exact SCOPE|exact DEFINITION|
     |reflexivity|reflexivity|unfold gateway_destructor_kind;auto 9|exact INPUT|exact RUN|exact NONNULL].
  intros memory current READY HOLD;eapply gateway_reference_negative_request;[exact HOLD|exact MEMBER].
Qed.
