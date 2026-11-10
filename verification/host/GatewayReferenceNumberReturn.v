(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The final real numeric return transfers its selected source
   temporary to the caller result while retaining the same scalar storage and held graph. *)
From Stdlib Require Import List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Machine ClightSteps StoreSteps LocalAccess.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayObjectDiscipline GatewayObjectThreads
  GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceThreads GatewayReferenceMoves GatewayReferenceNumberOwners GatewayReferenceNumericContext
  GatewayNumberSignSource GatewayJsonNumberSource GatewayNumberIntegerStructure GatewayPure GatewayReadonly GatewayOperations GatewayValueReturns
  GatewayScalarConstructorCalls GatewayFramedRuntime GatewayPathEvents GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.
Local Close Scope lean_scope.

Lemma gateway_number_sign_pure_return ge parameters selected memory:
  parameters!_value__1=Some selected->gateway_object_pointer_value selected->
  gateway_pure_path ge(State f_host_json_number number_sign_return(Kseq(json_number_rest number_sign_after)Kstop)empty_env parameters memory)selected.
Proof.
  intros SELECTED POINTER;eapply gateway_pure_next with(next:=Returnstate selected Kstop memory).
  - cbn;tauto.
  - intros;apply unchanged_store_edge;eapply edge_return with(v:=selected);
      [apply value_temp;exact SELECTED|destruct POINTER as[NULL|[object[offset SAME]]];subst selected;reflexivity].
  - constructor.
Qed.

Theorem gateway_reference_actual_number_return {World Event}(backend:gateway_backend World Event)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (reference_threads:gateway_reference_thread_contract backend(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    invocation ledger ticket held parameters selected scalar slots stream_block stream_offset initial readonly original size object bytes
    before world events value after next:
  gateway_reference_ledger_well_formed ledger->gateway_reference_owns ledger(number_current_owner invocation)ticket selected->
  gateway_reference_take(gateway_reference_result invocation)(gateway_reference_entries ledger)=None->
  parameters!_value__1=Some selected->gateway_object_pointer_value selected->
  gateway_reference_numeric_context python objects decimal_float detached stable heap_allocation ledger held
    scalar slots stream_block stream_offset initial readonly original size object bytes before world->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_json_number number_sign_return(Kseq(json_number_rest number_sign_after)Kstop)empty_env parameters before)world)events
    (gateway_live(Returnstate value Kstop after)next)->
  exists final,
    value=selected /\gateway_reference_apply(gateway_reference_move(number_current_owner invocation)(gateway_reference_result invocation))
      (gateway_reference_valid ledger)=gateway_reference_valid final /\gateway_reference_ledger_well_formed final /\
    gateway_reference_owns final(gateway_reference_result invocation)ticket selected /\
    gateway_reference_numeric_context python objects decimal_float detached stable heap_allocation final held
      scalar slots stream_block stream_offset initial readonly original size object bytes after next /\
    gateway_received_bytes io(stream_descriptor initial)events=[].
Proof.
  intros FORMED OWNED VACANT SELECTED POINTER[STORAGE SCOPE]RUN.
  destruct(gateway_reference_move_scope python objects decimal_float ledger(number_current_owner invocation)(gateway_reference_result invocation)
    ticket selected held world FORMED OWNED VACANT SCOPE)as(final &MOVE &WELL &CAPTURED &MOVED_SCOPE &COUNTS &OTHERS).
  pose proof(gateway_reference_numeric_ambient backend python objects decimal_float detached io stable thread_errno heap_allocation runtime reference_threads
    final held scalar slots stream_block stream_offset initial readonly original size object bytes)as CLOSED.
  destruct(gateway_pure_path_ready_return backend(Clight.globalenv prog)_ CLOSED
    (State f_host_json_number number_sign_return(Kseq(json_number_rest number_sign_after)Kstop)empty_env parameters before)selected world events value after next
    (gateway_number_sign_pure_return _ parameters selected before SELECTED POINTER)(conj STORAGE MOVED_SCOPE)RUN)as[SAME[READY QUIET]].
  exists final;split;[exact SAME|]. split;[exact MOVE|]. split;[exact WELL|]. split;[exact CAPTURED|]. split;[exact READY|].
  exact(gateway_quiet_received io(stream_descriptor initial)events QUIET).
Qed.
