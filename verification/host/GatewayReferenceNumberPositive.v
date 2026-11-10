(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual nonnegative sign branch returns its retained
   integer and transfers that exact source credit to the caller result. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayObjectDiscipline GatewayObjectThreads
  GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceHeld GatewayReferenceThreads GatewayReferenceNormalForm GatewayReferenceNumberOwners
  GatewayReferenceNumericContext GatewayReferenceNumericRequests GatewayReferenceNumberReturn GatewayNumberSignSource GatewayNumberIntegerStructure
  GatewaySourceSegments GatewayFramedRuntime GatewayPathEvents GatewayScalarConstructorCalls GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_reference_actual_number_positive {World Event}(backend:gateway_backend World Event)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (reference_threads:gateway_reference_thread_contract backend(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    invocation ledger ticket current current_offset integer tail held parameters ignored scalar slots stream_block stream_offset initial readonly original
    size object bytes before world events value after next:
  gateway_reference_ledger_well_formed ledger->
  gateway_reference_entries ledger=gateway_reference_entry ticket(number_current_owner invocation)(Vptr current current_offset)::tail->
  gateway_reference_take(gateway_reference_result invocation)(gateway_reference_entries ledger)=None->
  gateway_reference_numeric_context python objects decimal_float detached stable heap_allocation ledger
    (held++[gateway_reference_scalar_capture ticket(Vptr current current_offset)(gateway_long_object integer)])
    scalar slots stream_block stream_offset initial readonly original size object bytes before world->
  parameters!_negative=Some(Vint Int.zero)->parameters!_value__1=Some(Vptr current current_offset)->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Returnstate ignored(number_sign_base_cont parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists final,
    value=Vptr current current_offset /\
    gateway_reference_apply(gateway_reference_move(number_current_owner invocation)(gateway_reference_result invocation))
      (gateway_reference_valid ledger)=gateway_reference_valid final /\gateway_reference_ledger_well_formed final /\
    gateway_reference_entries final=gateway_reference_entry ticket(gateway_reference_result invocation)(Vptr current current_offset)::tail /\
    gateway_reference_next final=gateway_reference_next ledger /\
    gateway_reference_owns final(gateway_reference_result invocation)ticket(Vptr current current_offset) /\
    gateway_reference_numeric_context python objects decimal_float detached stable heap_allocation final
      (held++[gateway_reference_scalar_capture ticket(Vptr current current_offset)(gateway_long_object integer)])
      scalar slots stream_block stream_offset initial readonly original size object bytes after next /\
    gateway_received_bytes io(stream_descriptor initial)events=[].
Proof.
  intros FORMED ENTRIES VACANT INPUT POSITIVE CURRENT RUN.
  set(property:=gateway_reference_numeric_context python objects decimal_float detached stable heap_allocation ledger
    (held++[gateway_reference_scalar_capture ticket(Vptr current current_offset)(gateway_long_object integer)])
    scalar slots stream_block stream_offset initial readonly original size object bytes).
  pose proof(gateway_reference_numeric_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation runtime reference_threads
    ledger(held++[gateway_reference_scalar_capture ticket(Vptr current current_offset)(gateway_long_object integer)])
    scalar slots stream_block stream_offset initial readonly original size object bytes)as CLOSED.
  pose proof(gateway_number_positive_return_path backend(Clight.globalenv prog)property parameters ignored before CLOSED POSITIVE)as PATH.
  destruct(gateway_source_segment_cut backend(Clight.globalenv prog)_ _ _ _ PATH before world events value after next INPUT RUN)
    as(prefix &suffix &return_memory &return_world &EVENTS &QUIET &PREFIX &READY &REST).
  destruct(gateway_reference_actual_number_return backend python objects decimal_float detached io stable thread_errno heap_allocation runtime reference_threads
    invocation ledger ticket(held++[gateway_reference_scalar_capture ticket(Vptr current current_offset)(gateway_long_object integer)])parameters(Vptr current current_offset)
    scalar slots stream_block stream_offset initial readonly original size object bytes return_memory return_world suffix value after next
    FORMED ltac:(unfold gateway_reference_owns;rewrite ENTRIES;left;reflexivity)VACANT CURRENT ltac:(right;repeat eexists;reflexivity)READY REST)
    as(final &RETURNED &MOVE &WELL &OWNED &FINAL &EMPTY).
  destruct(gateway_reference_head_move _ _ _ _ _ _ _ ENTRIES MOVE)as[FINAL_ENTRIES FINAL_NEXT].
  exists final;split;[exact RETURNED|]. split;[exact MOVE|]. split;[exact WELL|]. split;[exact FINAL_ENTRIES|]. split;[exact FINAL_NEXT|].
  split;[exact OWNED|]. split;[exact FINAL|].
  rewrite EVENTS,gateway_received_append,(gateway_quiet_received io(stream_descriptor initial)prefix QUIET),EMPTY;reflexivity.
Qed.
