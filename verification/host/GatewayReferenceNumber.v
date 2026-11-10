(* SPDX-License-Identifier: Apache-2.0 *)
(* §FS-host-boundary.caller: The actual tag9 helper result reaches the enclosing scalar
   return through its checked native cleanup, preserving the same source-owned credit. *)
From Stdlib Require Import ZArith List Lia.
From compcert Require Import Coqlib Maps Integers AST Values Memory Events Globalenvs Ctypes Clight.
Require Import Machine.
From HostGateway Require Import GatewaySource GatewayMachine GatewayPython GatewayObjects GatewayReferences GatewayObjectDiscipline
  GatewayObjectThreads GatewayValue GatewayValueEntry GatewayValueContext GatewayValueStack GatewayScalarLength
  GatewayScalarBuffer GatewayScalarSizedFrames GatewayScalarNumberCall GatewayScalarTerminate GatewayScalarPayloadMemory GatewayScalarDecoding
  GatewayScalarReadPath GatewayScalarBytesPath GatewayScalarConstructorCalls GatewayReferenceJsonNumber GatewayReferenceNumericContext GatewayReferenceNumericRequests
  GatewayReferenceScalarTransfer GatewayRegionThreads GatewayNativeRegions GatewayNativeMemory GatewayObjectEvents GatewayPathEvents GatewayStreamInterface GatewayThreadRuntime
  GatewayReferenceLedger GatewayReferencePlaces GatewayReferenceAccounting GatewayReferenceHeld GatewayReferenceThreads GatewayReferenceNormalForm GatewayThreadInvariant.
Import ListNotations.
Local Close Scope lean_scope.
Open Scope Z_scope.

Theorem gateway_reference_actual_number_value {World Event}(backend:gateway_backend World Event)
    python objects decimal_float detached io stable thread_errno heap_allocation
    (runtime:gateway_thread_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)thread_errno)
    (allocations:gateway_native_memory_runtime backend io(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)heap_allocation)
    (constructors:gateway_objects_runtime backend python objects decimal_float)
    (references:gateway_reference_runtime backend python objects)
    (reference_threads:gateway_reference_thread_contract backend(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)heap_allocation python objects)
    (io_projection:gateway_direct_io_projection backend io)
    context ledger held slots parameters stream_block stream_offset initial readonly original size object bytes before world events value after next mode_symbol:
  gateway_reference_ledger_well_formed ledger->
  (forall identifier,gateway_reference_take(gateway_reference_temporary(S(gateway_reference_depth context))identifier)(gateway_reference_entries ledger)=None)->
  gateway_reference_take(gateway_reference_result(S(gateway_reference_depth context)))(gateway_reference_entries ledger)=None->
  gateway_reference_take(gateway_reference_result(gateway_reference_depth context))(gateway_reference_entries ledger)=None->
  gateway_reference_scope python objects decimal_float ledger held world->
  Genv.find_symbol(Clight.globalenv prog)___stringlit_8=Some mode_symbol->
  gateway_unicode_strict_mode original(Vptr mode_symbol Ptrofs.zero)->
  (forall candidate position,gateway_scalar_mode_region mode_symbol candidate position->readonly candidate position)->
  parameters!_bytes=Some(Vptr object Ptrofs.zero)->Int64.unsigned size<=65536->
  gateway_scalar_payload_ready(fun current candidate=>gateway_native_private(python current)candidate)stable
    (gateway_python_discipline python objects detached)heap_allocation gateway_scalar_number slots stream_block stream_offset initial readonly original
    size object bytes before world->
  (forall candidate position,readonly candidate position->gateway_native_private(python world)candidate)->
  gateway_steps backend(Clight.globalenv prog)
    (gateway_live(Returnstate(Vint Int.zero)(gateway_scalar_read_cont slots parameters)before)world)events
    (gateway_live(Returnstate value Kstop after)next)->value<>Vnullptr->
  exists final ticket description,
    gateway_json_number bytes /\gateway_scalar_semantics decimal_float 9 bytes description /\
    gateway_reference_ledger_well_formed final /\(gateway_reference_next ledger<=ticket)%nat /\
    gateway_reference_owns final(gateway_reference_result(gateway_reference_depth context))ticket value /\
    gateway_reference_place_value(Clight.globalenv prog)(Returnstate value context after)
      (gateway_reference_result(gateway_reference_depth context))value /\
    gateway_reference_scope python objects decimal_float final(held++[gateway_reference_scalar_capture ticket value description])next /\
    gateway_value_context(fun current candidate=>gateway_native_private(python current)candidate)stable
      (gateway_python_discipline python objects detached)stream_block stream_offset initial readonly original after next /\
    (forall candidate position,readonly candidate position->gateway_native_private(python next)candidate) /\
    gateway_value_heap decimal_float(objects next)value(gateway_wire_scalar 9 bytes) /\
    gateway_received_bytes io(stream_descriptor initial)events=[] /\
    gateway_reference_result_entries context ledger final ticket value.
Proof.
  intros FORMED TEMP_FREE CHILD_FREE RESULT_FREE SCOPE MODE_SYMBOL MODE MODE_REGION BUFFER MAXIMUM INPUT READONLY RUN NONNULL.
  set(native:=fun current candidate=>gateway_native_private(python current)candidate).
  set(base:=gateway_python_discipline python objects detached).
  set(scoped:=gateway_thread_invariant_discipline base(gateway_reference_scope python objects decimal_float ledger held)).
  pose proof(gateway_thread_with_reference_scope backend io native stable base thread_errno heap_allocation python objects decimal_float
    reference_threads ledger held runtime)as SCOPED_RUNTIME.
  set(augmented:=gateway_native_region_discipline native scoped readonly).
  pose proof(gateway_thread_with_native_region backend io native stable scoped thread_errno SCOPED_RUNTIME readonly)as THREADS.
  assert(OWNED:gateway_native_region_owned native readonly before world).
  { destruct INPUT as[[[[[[SIDE[STREAM[STABLE[RAW FRAME]]]]SLOTS]TAG]SIZE]REST]PAYLOAD].
    intros candidate position READ;split;
      [exact(gateway_value_readonly_live _ _ _ _ _ RAW candidate position READ)|apply READONLY with(position:=position);exact READ]. }
  assert(AUGMENTED_INPUT:gateway_scalar_payload_ready native stable augmented heap_allocation gateway_scalar_number slots stream_block stream_offset
    initial readonly original size object bytes before world).
  { destruct INPUT as[READY PAYLOAD];split;[|exact PAYLOAD]. pose proof READY as[_[[SIDE HEAP]SEPARATE]].
    eapply gateway_scalar_buffer_rebase;[exact READY|]. split;[split;[exact SIDE|exact SCOPE]|exact OWNED]. }
  destruct(gateway_actual_number_constructor_cut backend io native stable augmented thread_errno THREADS heap_allocation slots parameters
    stream_block stream_offset initial readonly original size object bytes before world events value after next BUFFER AUGMENTED_INPUT RUN NONNULL)
    as(called_parameters &prefix &constructing &suffix &constructor_before &constructor_world &constructor_after &constructor_next &
      EVENTS &QUIET &CALLED_BUFFER &AUGMENTED_READY &CONSTRUCTOR_RUN &REST).
  pose proof(gateway_scalar_terminated_side native stable augmented heap_allocation gateway_scalar_number slots stream_block stream_offset initial readonly original
    size object bytes constructor_before constructor_world AUGMENTED_READY)as[CALLED_SIDE CALLED_OWNED].
  assert(READY:gateway_scalar_private_ready python objects detached stable heap_allocation gateway_scalar_number slots stream_block stream_offset
    initial readonly original size object bytes constructor_before constructor_world).
  { split;[eapply gateway_scalar_terminated_rebase;[exact AUGMENTED_READY|exact(proj1 CALLED_SIDE)]|].
    intros candidate position READ;exact(proj2(CALLED_OWNED candidate position READ)). }
  destruct(gateway_reference_actual_json_number backend python objects decimal_float detached io stable thread_errno heap_allocation
    runtime constructors references reference_threads io_projection(S(gateway_reference_depth context))ledger held gateway_scalar_number slots
    stream_block stream_offset initial readonly original size object bytes mode_symbol constructor_before constructor_world constructing value constructor_after constructor_next
    FORMED TEMP_FREE CHILD_FREE(proj2 CALLED_SIDE)READY MAXIMUM MODE_SYMBOL MODE MODE_REGION CONSTRUCTOR_RUN NONNULL)
    as(intermediate &ticket &description &JSON &DECODED &WELL &TICKET_BOUND &ENTRIES &OWNER &[AFTER_READY HELD_SCOPE] &HELPER_EMPTY).
  destruct(gateway_reference_actual_scalar_transfer backend python objects decimal_float detached io stable thread_errno heap_allocation
    runtime allocations reference_threads context ledger intermediate ticket(held++[gateway_reference_scalar_capture ticket value description])
    _t'20 gateway_scalar_number slots called_parameters stream_block stream_offset initial readonly original size object constructor_after constructor_next suffix
    value value after next ltac:(discriminate)CALLED_BUFFER WELL ENTRIES OWNER RESULT_FREE(proj1(proj1(proj1 AFTER_READY)))HELD_SCOPE(proj2 AFTER_READY)REST)
    as(final &SAME &FINAL_WELL &FINAL_ENTRIES &FINAL_OWNER &BINDING &FINAL_CONTEXT &HELD_FINAL &FINAL_NATIVE &CLEANUP_EMPTY &TRANSFER).
  assert(LOOKUP:gateway_object_values(objects next)value=Some description).
  { pose proof(proj2 HELD_FINAL)as CAPTURED;apply Forall_app in CAPTURED;destruct CAPTURED as[OLD NEW].
    destruct(Forall_inv NEW)as[CAPTURED_OWNER[PRIVATE[DESTRUCTIBLE[DESCRIBED CHILDREN]]]];exact DESCRIBED. }
  exists final,ticket,description;split;[exact JSON|]. split;[exact DECODED|]. split;[exact FINAL_WELL|]. split;[exact TICKET_BOUND|].
  split;[exact FINAL_OWNER|]. split;[exact BINDING|]. split;[exact HELD_FINAL|]. split;[exact FINAL_CONTEXT|]. split;[exact FINAL_NATIVE|].
  split;[eapply gateway_heap_scalar;[exact LOOKUP|exact DECODED]|]. split;[|exact FINAL_ENTRIES].
  rewrite EVENTS,!gateway_received_append,(gateway_quiet_received io(stream_descriptor initial)prefix QUIET),HELPER_EMPTY,CLEANUP_EMPTY;reflexivity.
Qed.
