(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: Final base cleanup and optional negation return exactly the
   same source-produced signed integer with one retained caller-result reference. *)
From Stdlib Require Import ZArith List.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayObjectDiscipline GatewayObjectThreads
  GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceHeld GatewayReferenceThreads GatewayReferenceNormalForm GatewayReferenceNumberOwners
  GatewayReferenceNumericFrames GatewayReferenceNumericContext GatewayReferenceNumericRequests GatewayReferenceNumberBaseRelease GatewayReferenceNumberPositive GatewayReferenceNumberNegative
  GatewayNumberSignSource GatewayNumberIntegerStructure GatewayFramedRuntime GatewayPathEvents GatewayObjectEvents GatewayScalarConstructorCalls GatewayStreamInterface GatewayThreadRuntime.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Theorem gateway_reference_actual_number_sign {World Event}(backend:gateway_backend World Event)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (constructors:gateway_objects_runtime backend python objects decimal_float)
    (references:gateway_reference_runtime backend python objects)
    (reference_threads:gateway_reference_thread_contract backend(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (projection:gateway_direct_io_projection backend io)
    (negative:bool)invocation ledger current_ticket current current_offset integer base_ticket base base_offset tail held parameters
    scalar slots stream_block stream_offset initial readonly original size object bytes before world events value after next:
  gateway_reference_ledger_well_formed ledger->
  gateway_reference_entries ledger=
    gateway_reference_entry current_ticket(number_current_owner invocation)(Vptr current current_offset)::
    gateway_reference_entry base_ticket(number_base_owner invocation)(Vptr base base_offset)::tail->
  gateway_reference_take(number_signed_owner invocation)(gateway_reference_entries ledger)=None->
  gateway_reference_take(gateway_reference_result invocation)(gateway_reference_entries ledger)=None->
  (forall captured,In captured held->gateway_held_ticket captured<>current_ticket /\gateway_held_ticket captured<>base_ticket)->
  gateway_reference_scope python objects decimal_float ledger
    (held++[gateway_reference_scalar_capture base_ticket(Vptr base base_offset)(gateway_long_object 1000000000);
      gateway_reference_scalar_capture current_ticket(Vptr current current_offset)(gateway_long_object integer)])world->
  gateway_scalar_private_ready python objects detached stable heap_allocation scalar slots stream_block stream_offset initial readonly original
    size object bytes before world->parameters!_base=Some(Vptr base base_offset)->parameters!_value__1=Some(Vptr current current_offset)->
  parameters!_negative=Some(Vint(if negative then Int.one else Int.zero))->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(State f_host_json_number Sskip number_integer_loop_cont empty_env parameters before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  exists final,
    gateway_reference_ledger_well_formed final /\
    gateway_reference_next final=(if negative then S(gateway_reference_next ledger)else gateway_reference_next ledger) /\
    gateway_reference_entries final=gateway_reference_entry(if negative then gateway_reference_next ledger else current_ticket)
      (gateway_reference_result invocation)value::tail /\
    gateway_reference_owns final(gateway_reference_result invocation)(if negative then gateway_reference_next ledger else current_ticket)value /\
    gateway_reference_numeric_context python objects decimal_float detached stable heap_allocation final
      (held++[gateway_reference_scalar_capture(if negative then gateway_reference_next ledger else current_ticket)value
        (gateway_long_object(if negative then -integer else integer))])
      scalar slots stream_block stream_offset initial readonly original size object bytes after next /\
    gateway_received_bytes io(stream_descriptor initial)events=[].
Proof.
  intros FORMED ENTRIES SIGNED_FREE RESULT_FREE DIFFERENT SCOPE INPUT BASE CURRENT NEGATIVE RUN NONNULL.
  destruct(gateway_reference_actual_number_base_release backend python objects decimal_float detached io stable thread_errno heap_allocation runtime references reference_threads
    projection invocation ledger current_ticket current current_offset integer base_ticket base base_offset tail held parameters
    scalar slots stream_block stream_offset initial readonly original size object bytes before world events value after next FORMED ENTRIES
    ltac:(intros captured MEMBER;exact(proj2(DIFFERENT captured MEMBER)))SCOPE INPUT BASE RUN)
    as(released &prefix &suffix &released_memory &released_world &ignored &RELEASE &RELEASED_WELL &RELEASED_NEXT &RELEASED_ENTRIES &CURRENT_OWNED
      &RELEASED_READY &EVENTS &EMPTY &PREFIX &REST).
  assert(SIGNED_VACANT:gateway_reference_take(number_signed_owner invocation)(gateway_reference_entries released)=None).
  { eapply gateway_reference_numeric_release_keeps_vacant;[exact SIGNED_FREE|exact RELEASE]. }
  assert(RESULT_VACANT:gateway_reference_take(gateway_reference_result invocation)(gateway_reference_entries released)=None).
  { eapply gateway_reference_numeric_release_keeps_vacant;[exact RESULT_FREE|exact RELEASE]. }
  destruct negative.
  - destruct(gateway_reference_actual_number_negative backend python objects decimal_float detached io stable thread_errno heap_allocation runtime constructors references reference_threads
      projection invocation released current_ticket current current_offset integer tail held parameters ignored
      scalar slots stream_block stream_offset initial readonly original size object bytes released_memory released_world suffix value after next
      RELEASED_WELL RELEASED_ENTRIES SIGNED_VACANT RESULT_VACANT
      ltac:(intros captured MEMBER;exact(proj1(DIFFERENT captured MEMBER)))RELEASED_READY NEGATIVE CURRENT REST NONNULL)
      as(final &WELL &NEXT &FINAL_ENTRIES &OWNED &FINAL &FINAL_EMPTY).
    exists final;split;[exact WELL|]. split;[rewrite NEXT,RELEASED_NEXT;reflexivity|].
    split;[rewrite<-RELEASED_NEXT;exact FINAL_ENTRIES|]. split;[rewrite<-RELEASED_NEXT;exact OWNED|].
    split;[rewrite<-RELEASED_NEXT;exact FINAL|]. rewrite EVENTS,gateway_received_append,EMPTY,FINAL_EMPTY;reflexivity.
  - destruct(gateway_reference_actual_number_positive backend python objects decimal_float detached io stable thread_errno heap_allocation runtime reference_threads
      invocation released current_ticket current current_offset integer tail held parameters ignored
      scalar slots stream_block stream_offset initial readonly original size object bytes released_memory released_world suffix value after next
      RELEASED_WELL RELEASED_ENTRIES RESULT_VACANT RELEASED_READY NEGATIVE CURRENT REST)
      as(final &RETURNED &MOVE &WELL &FINAL_ENTRIES &NEXT &OWNED &FINAL &FINAL_EMPTY).
    rewrite RETURNED in *.
    exists final;split;[exact WELL|]. split;[rewrite NEXT,RELEASED_NEXT;reflexivity|]. split;[exact FINAL_ENTRIES|]. split;[exact OWNED|].
    split;[exact FINAL|]. rewrite EVENTS,gateway_received_append,EMPTY,FINAL_EMPTY;reflexivity.
Qed.
