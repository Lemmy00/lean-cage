(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The same actual number helper decodes its text, converts it
   once and releases that transient reference before returning its retained float. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayObjectDiscipline
  GatewayObjectThreads GatewayReferenceLedger GatewayReferenceAccounting GatewayReferenceHeld GatewayReferenceThreads GatewayReferenceNormalForm
  GatewayReferenceNumericContext GatewayReferenceNumericRequests GatewayReferenceNumericText GatewayReferenceNumericNormalForm GatewayReferenceFloatTail
  GatewayReferenceAncestors GatewayReferenceStackBound GatewayNumberFloatSource GatewayNumberConstruction GatewayContexts
  GatewayScalarConstructorCalls GatewayScalarDecoding GatewayScalarLength GatewayObjectRuns GatewayObjectEvents GatewayFramedRuntime GatewayStreamInterface GatewayThreadRuntime
  GatewayPathEvents.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Theorem gateway_reference_actual_float_construction {World Event}(backend:gateway_backend World Event)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (constructors:gateway_objects_runtime backend python objects decimal_float)
    (references:gateway_reference_runtime backend python objects)
    (reference_threads:gateway_reference_thread_contract backend(fun current object=>gateway_native_private(python current)object)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (projection:gateway_direct_io_projection backend io)
    ledger text_owner result_owner held parameters definition scalar slots stream_block stream_offset initial readonly original
    size object bytes mode_symbol before world events value after next:
  gateway_reference_ledger_well_formed ledger->
  gateway_reference_take text_owner(gateway_reference_entries ledger)=None->
  gateway_reference_take result_owner(gateway_reference_entries ledger)=None->text_owner<>result_owner->
  gateway_reference_scope python objects decimal_float ledger held world->
  gateway_object_api_definition gateway_api_unicode_utf8=Some definition->
  gateway_scalar_private_ready python objects detached stable heap_allocation scalar slots stream_block stream_offset initial readonly original
    size object bytes before world->Int64.unsigned size<=65536->
  gateway_unicode_strict_mode original(Vptr mode_symbol Ptrofs.zero)->
  (forall candidate position,gateway_scalar_mode_region mode_symbol candidate position->readonly candidate position)->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Callstate definition[Vptr object Ptrofs.zero;Vlong size;Vptr mode_symbol Ptrofs.zero](gateway_number_decode_cont parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  exists final characters floating,
    gateway_utf8_text bytes characters /\decimal_float characters floating /\
    gateway_reference_ledger_well_formed final /\gateway_reference_owns final result_owner(S(gateway_reference_next ledger))value /\
    gateway_reference_entries final=gateway_reference_entry(S(gateway_reference_next ledger))result_owner value::gateway_reference_entries ledger /\
    gateway_reference_next final=S(S(gateway_reference_next ledger)) /\
    gateway_reference_numeric_context python objects decimal_float detached stable heap_allocation final
      (held++[gateway_reference_scalar_capture(S(gateway_reference_next ledger))value(gateway_float_object floating)])
      scalar slots stream_block stream_offset initial readonly original size object bytes after next /\
    gateway_received_bytes io(stream_descriptor initial)events=[].
Proof.
  intros FORMED TEXT_VACANT RESULT_VACANT DISTINCT SCOPE DEFINITION INPUT MAXIMUM MODE MODE_REGION RUN NONNULL.
  destruct(gateway_return_cut backend(Clight.globalenv prog)definition[Vptr object Ptrofs.zero;Vlong size;Vptr mode_symbol Ptrofs.zero]
    (gateway_number_decode_cont parameters)before world events(Returnstate value Kstop after)next ltac:(cbn;exact I)ltac:(cbn;lia)RUN)
    as(decoding &suffix &text &decoded &decoded_world &EVENTS &DECODE &REST).
  assert(TEXT_NONNULL:text<>Vnullptr).
  { intro NULL;subst text;apply NONNULL.
    exact(gateway_number_null_text_denied backend(Clight.globalenv prog)parameters decoded decoded decoded_world suffix value after next REST). }
  destruct(gateway_reference_actual_numeric_text backend(Clight.globalenv prog)python objects decimal_float detached io stable thread_errno heap_allocation
    runtime constructors reference_threads ledger text_owner held definition scalar slots stream_block stream_offset initial readonly original size object bytes mode_symbol
    before world decoding text decoded decoded_world FORMED TEXT_VACANT SCOPE DEFINITION INPUT MAXIMUM MODE MODE_REGION DECODE TEXT_NONNULL)
    as(characters &text_ledger &TEXT &TEXT_MINT &TEXT_WELL &TEXT_OWNED &TEXT_STORAGE &TEXT_SCOPE).
  destruct(gateway_reference_mint_entries _ _ _ _ TEXT_MINT)as[TEXT_ENTRIES TEXT_NEXT].
  assert(RESULT_FREE:gateway_reference_take result_owner(gateway_reference_entries text_ledger)=None).
  { eapply GatewayReferenceStackBound.gateway_reference_mint_keeps_vacant;[exact RESULT_VACANT|exact DISTINCT|exact TEXT_MINT]. }
  assert(DIFFERENT:forall captured,In captured held->gateway_held_ticket captured<>gateway_reference_next ledger).
  { intros captured MEMBER SAME.
    pose proof(gateway_reference_scope_ticket_bound python objects decimal_float ledger held world captured FORMED SCOPE MEMBER)as BOUND;lia. }
  destruct(gateway_reference_actual_float_tail backend python objects decimal_float detached io stable thread_errno heap_allocation runtime constructors references reference_threads
    projection text_ledger text_owner(gateway_reference_next ledger)text characters result_owner held parameters scalar slots stream_block stream_offset initial readonly original
    size object bytes decoded decoded_world suffix value after next TEXT_WELL TEXT_OWNED RESULT_FREE DIFFERENT TEXT_SCOPE TEXT_STORAGE REST NONNULL)
    as(final &floating &constructed &DECIMAL &MINT &RELEASE &FINAL_WELL &FINAL_OWNED &FINAL_CONTEXT &EMPTY).
  destruct(gateway_reference_mint_entries _ _ _ _ MINT)as[FLOAT_ENTRIES FLOAT_NEXT].
  destruct(gateway_reference_numeric_middle_release constructed final(gateway_reference_entries ledger)
    (gateway_reference_next text_ledger)result_owner value(gateway_reference_next ledger)text_owner text DISTINCT
    ltac:(rewrite FLOAT_ENTRIES,TEXT_ENTRIES;reflexivity)RELEASE)as[ENTRIES NEXT].
  exists final,characters,floating;split;[exact TEXT|]. split;[exact DECIMAL|]. split;[exact FINAL_WELL|].
  split;[rewrite<-TEXT_NEXT;exact FINAL_OWNED|]. split;[rewrite<-TEXT_NEXT;exact ENTRIES|].
  split;[rewrite NEXT,FLOAT_NEXT,TEXT_NEXT;reflexivity|]. split;[rewrite<-TEXT_NEXT;exact FINAL_CONTEXT|].
  rewrite EVENTS,gateway_received_append,EMPTY.
  rewrite(gateway_object_run_no_direct_receive backend(Clight.globalenv prog)io gateway_api_unicode_utf8 definition
    [Vptr object Ptrofs.zero;Vlong size;Vptr mode_symbol Ptrofs.zero]before world decoding text decoded decoded_world
    (stream_descriptor initial)projection DEFINITION DECODE);reflexivity.
Qed.
