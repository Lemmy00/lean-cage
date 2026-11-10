(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Actual signed and unsigned long SDK calls mint the exact
   machine-width operand value while retaining independently owned cached aliases. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Integers AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayObjectDiscipline
  GatewayObjectThreads GatewayReferenceLedger GatewayReferenceThreads GatewayReferenceNumericStorage GatewayReferenceNumericRequests
  GatewayScalarConstructorCalls GatewayScalarLength GatewayFramedRuntime GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_reference_actual_literal_storage {World Event}(backend:gateway_backend World Event)(ge:Clight.genv)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (constructors:gateway_objects_runtime backend python objects decimal_float)
    (reference_threads:gateway_reference_thread_contract backend(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (unsigned:bool)ledger owner held definition word scalar slots stream_block stream_offset initial readonly original
    size object bytes before world events result after next:
  gateway_reference_ledger_well_formed ledger->gateway_reference_take owner(gateway_reference_entries ledger)=None->
  gateway_reference_scope python objects decimal_float ledger held world->
  gateway_object_api_definition(if unsigned then gateway_api_long_unsigned else gateway_api_long_signed)=Some definition->
  gateway_scalar_private_ready python objects detached stable heap_allocation scalar slots stream_block stream_offset initial readonly original
    size object bytes before world->
  gateway_steps backend ge(gateway_live(Callstate definition[Vlong word]Kstop before)world)events
    (gateway_live(Returnstate result Kstop after)next)->result<>Vnullptr->
  exists final,
    gateway_reference_apply(gateway_reference_mint owner result)(gateway_reference_valid ledger)=gateway_reference_valid final /\
    gateway_reference_ledger_well_formed final /\gateway_reference_owns final owner(gateway_reference_next ledger)result /\
    gateway_scalar_private_ready python objects detached stable heap_allocation scalar slots stream_block stream_offset initial readonly original
      size object bytes after next /\
    gateway_reference_scope python objects decimal_float final
      (held++[gateway_reference_scalar_capture(gateway_reference_next ledger)result
        (gateway_long_object(if unsigned then Int64.unsigned word else Int64.signed word))])next.
Proof.
  intros FORMED VACANT SCOPE DEFINITION INPUT RUN NONNULL.
  eapply gateway_reference_actual_numeric_storage;
    [exact runtime|exact constructors|exact reference_threads|exact FORMED|exact VACANT|exact SCOPE|exact DEFINITION|
     |reflexivity|reflexivity|unfold gateway_destructor_kind;auto 9|exact INPUT|exact RUN|exact NONNULL].
  intros memory current READY HELD;destruct unsigned;split;
    first[apply gateway_request_long_unsigned|apply gateway_request_long_signed|exact I].
Qed.
