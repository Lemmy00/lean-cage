(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The checked constructor-return, assignment, native free and
   outer return transfer the same source credit without a Python reference release. *)
From Stdlib Require Import List PeanoNat Lia.
From compcert Require Import Maps Integers Values Memory Clight.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayObjectDiscipline
  GatewayObjectThreads GatewayValueEntry GatewayScalarLength GatewayScalarBuffer GatewayScalarBytesPath GatewayReferenceScalarCleanup
  GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting GatewayReferenceThreads GatewayReferenceMoves
  GatewayReferenceNormalForm GatewayPathEvents GatewayValueContext GatewayNativeMemory GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.
Local Close Scope lean_scope.

Theorem gateway_reference_actual_scalar_transfer {World Event}(backend:gateway_backend World Event)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (allocations:gateway_native_memory_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)heap_allocation)
    (reference_threads:gateway_reference_thread_contract backend(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    context original_ledger ledger ticket held identifier scalar slots parameters stream_block stream_offset initial readonly original
    size object before world events returned value after next:
  identifier<>_bytes->parameters!_bytes=Some(Vptr object Ptrofs.zero)->
  gateway_reference_ledger_well_formed ledger->
  gateway_reference_entries ledger=gateway_reference_entry ticket(gateway_reference_result(S(gateway_reference_depth context)))returned::
    gateway_reference_entries original_ledger->
  gateway_reference_owns ledger(gateway_reference_result(S(gateway_reference_depth context)))ticket returned->
  gateway_reference_take(gateway_reference_result(gateway_reference_depth context))(gateway_reference_entries original_ledger)=None->
  gateway_scalar_buffer_ready(fun current candidate=>gateway_native_private(python current)candidate)stable
    (gateway_python_discipline python objects detached)heap_allocation scalar slots stream_block stream_offset initial readonly original size object before world->
  gateway_reference_scope python objects decimal_float ledger held world->
  (forall candidate position,readonly candidate position->gateway_native_private(python world)candidate)->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Returnstate returned(gateway_scalar_constructor_cont identifier slots parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists final,
    value=returned /\gateway_reference_ledger_well_formed final /\
    gateway_reference_result_entries context original_ledger final ticket returned /\
    gateway_reference_owns final(gateway_reference_result(gateway_reference_depth context))ticket returned /\
    gateway_reference_place_value(Clight.globalenv prog)(Returnstate value context after)
      (gateway_reference_result(gateway_reference_depth context))returned /\
    gateway_value_context(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)stream_block stream_offset initial readonly original after next /\
    gateway_reference_scope python objects decimal_float final held next /\
    (forall candidate position,readonly candidate position->gateway_native_private(python next)candidate) /\
    gateway_received_bytes io(stream_descriptor initial)events=[] /\
    gateway_reference_apply(gateway_reference_move(gateway_reference_result(S(gateway_reference_depth context)))
      (gateway_reference_result(gateway_reference_depth context)))(gateway_reference_valid ledger)=gateway_reference_valid final.
Proof.
  intros DISTINCT BUFFER WELL ENTRIES OWNER VACANT READY SCOPE READONLY RUN.
  destruct(gateway_reference_actual_scalar_cleanup backend python objects decimal_float detached io stable thread_errno heap_allocation
    runtime allocations reference_threads ledger held identifier scalar slots parameters stream_block stream_offset initial readonly original
    size object before world events returned value after next DISTINCT BUFFER READY SCOPE READONLY RUN)
    as[SAME[[FINAL_CONTEXT[FINAL_SCOPE FINAL_NATIVE]]EMPTY]].
  assert(FREE:gateway_reference_take(gateway_reference_result(gateway_reference_depth context))(gateway_reference_entries ledger)=None).
  { rewrite ENTRIES;cbn[gateway_reference_take gateway_reference_entry gateway_reference_owner].
    destruct(gateway_reference_place_eq(gateway_reference_result(gateway_reference_depth context))
      (gateway_reference_result(S(gateway_reference_depth context))));[injection e;intros;lia|rewrite VACANT;reflexivity]. }
  destruct(gateway_reference_move_scope python objects decimal_float ledger
    (gateway_reference_result(S(gateway_reference_depth context)))(gateway_reference_result(gateway_reference_depth context))
    ticket returned held next WELL OWNER FREE FINAL_SCOPE)as(final &MOVE &FORMED &OWNED &HELD &COUNTS &OTHERS).
  exists final;split;[exact SAME|]. split;[exact FORMED|]. split.
  - exact(proj1(gateway_reference_head_move ledger final(gateway_reference_entries original_ledger)ticket
      (gateway_reference_result(S(gateway_reference_depth context)))(gateway_reference_result(gateway_reference_depth context))returned ENTRIES MOVE)).
  - split;[exact OWNED|]. split;[rewrite SAME;apply gateway_reference_result_binding|].
    split;[exact FINAL_CONTEXT|]. split;[exact HELD|]. split;[exact FINAL_NATIVE|]. split;assumption.
Qed.
